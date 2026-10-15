/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.vmt.analysis.mdd;

import com.google.common.collect.MapMaker;
import hu.bme.mit.delta.mdd.LatticeDefinition;
import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentMap;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

/**
 * The formula operations the formula-backed MDD nodes need: substitution and simplification,
 * free-variable queries, and the mapping between MDD edge keys and solver values.
 *
 * <p>Edge keys are ints: booleans map to 0 and 1, integers to their value, and bitvectors of at
 * most 32 bits to their unsigned value (wrapped into the int range for 32 bits).
 */
public final class FormulaMddContext {

    private final FormulaManager fmgr;
    private final BooleanFormulaManager bmgr;
    private final FormulaProverPool proverPool;
    private final List<FormulaVar> modelVars;
    private final int edgeLimit;
    private FormulaMddEncoder encoder;

    // free variables of a formula object; identity keys, so a miss only costs a recomputation
    private final ConcurrentMap<Formula, Set<String>> variableCache =
            new MapMaker().weakKeys().makeMap();

    public static final int DEFAULT_EDGE_LIMIT = 1000;

    /**
     * @param modelVars the variables of all MDD levels, the ones read from solver models
     */
    public FormulaMddContext(
            FormulaManager fmgr,
            FormulaProverPool proverPool,
            Collection<FormulaVar> modelVars,
            int edgeLimit) {
        this.fmgr = fmgr;
        this.bmgr = fmgr.getBooleanFormulaManager();
        this.proverPool = proverPool;
        this.modelVars = List.copyOf(modelVars);
        this.edgeLimit = edgeLimit;
    }

    public FormulaMddContext(
            FormulaManager fmgr, FormulaProverPool proverPool, Collection<FormulaVar> modelVars) {
        this(fmgr, proverPool, modelVars, DEFAULT_EDGE_LIMIT);
    }

    public FormulaManager getFormulaManager() {
        return fmgr;
    }

    public BooleanFormulaManager getBooleanFormulaManager() {
        return bmgr;
    }

    public FormulaProverPool getProverPool() {
        return proverPool;
    }

    public FormulaMddEncoder getEncoder() {
        if (encoder == null) encoder = new FormulaMddEncoder(this);
        return encoder;
    }

    /** The values of the MDD level variables in the prover's current model. */
    public Map<String, Object> model(FormulaProver prover) {
        return prover.model(modelVars);
    }

    /** The largest number of edges a node may have before the check gives up. */
    public int getEdgeLimit() {
        return edgeLimit;
    }

    public LatticeDefinition<BooleanFormula> latticeDefinition() {
        return new LatticeDefinition<>(
                BooleanFormula.class,
                bmgr.makeFalse(),
                bmgr.makeTrue(),
                (a, b) -> bmgr.or(a, b),
                (a, b) -> bmgr.and(a, b),
                (a, b) -> bmgr.and(a, bmgr.not(b)));
    }

    public static boolean isSupported(FormulaType<?> type) {
        return type.isBooleanType()
                || type.isIntegerType()
                || (type.isBitvectorType()
                        && ((FormulaType.BitvectorType) type).getSize() <= Integer.SIZE);
    }

    // ---- simplification and variables ----

    public BooleanFormula simplify(BooleanFormula formula) {
        try {
            return fmgr.simplify(formula);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException(e);
        }
    }

    public BooleanFormula substitute(
            BooleanFormula formula, Map<? extends Formula, ? extends Formula> substitution) {
        return fmgr.substitute(formula, substitution);
    }

    public BooleanFormula substituteAndSimplify(
            BooleanFormula formula, Formula var, Formula value) {
        return simplify(fmgr.substitute(formula, Map.of(var, value)));
    }

    public Set<String> variables(Formula formula) {
        return variableCache.computeIfAbsent(
                formula, f -> Set.copyOf(fmgr.extractVariables(f).keySet()));
    }

    public boolean contains(Formula formula, FormulaVar var) {
        return variables(formula).contains(var.name());
    }

    public boolean isTrue(BooleanFormula formula) {
        return bmgr.isTrue(formula);
    }

    public boolean isFalse(BooleanFormula formula) {
        return bmgr.isFalse(formula);
    }

    @SuppressWarnings("unchecked")
    public BooleanFormula equal(Formula a, Formula b, FormulaType<?> type) {
        if (type.isBooleanType()) {
            return bmgr.equivalence((BooleanFormula) a, (BooleanFormula) b);
        }
        if (type.isIntegerType()) {
            return fmgr.getIntegerFormulaManager().equal((IntegerFormula) a, (IntegerFormula) b);
        }
        if (type.isBitvectorType()) {
            return fmgr.getBitvectorFormulaManager()
                    .equal((BitvectorFormula) a, (BitvectorFormula) b);
        }
        throw new UnsupportedOperationException("Unsupported variable type: " + type);
    }

    public BooleanFormula equal(FormulaVar var, Formula value) {
        return equal(var.formula(), value, var.type());
    }

    // ---- edge keys and values ----

    public int toKey(Object value, FormulaVar var) {
        final FormulaType<?> type = var.type();
        if (type.isBooleanType()) {
            return ((Boolean) value) ? 1 : 0;
        }
        if (type.isIntegerType()) {
            return ((BigInteger) value).intValueExact();
        }
        if (type.isBitvectorType()) {
            return ((BigInteger) value).intValue();
        }
        throw new UnsupportedOperationException("Unsupported variable type: " + type);
    }

    /** The solver value of an edge key, or null if the key is not a value of the type. */
    public Object toValue(int key, FormulaVar var) {
        final FormulaType<?> type = var.type();
        if (type.isBooleanType()) {
            if (key < 0 || key > 1) return null;
            return key == 1;
        }
        if (type.isIntegerType()) {
            return BigInteger.valueOf(key);
        }
        if (type.isBitvectorType()) {
            final int size = ((FormulaType.BitvectorType) type).getSize();
            final BigInteger unsigned =
                    BigInteger.valueOf(key)
                            .and(BigInteger.ONE.shiftLeft(size).subtract(BigInteger.ONE));
            if (size < Integer.SIZE && !unsigned.equals(BigInteger.valueOf(key))) return null;
            return unsigned;
        }
        throw new UnsupportedOperationException("Unsupported variable type: " + type);
    }

    /** The constant formula of an edge key, or null if the key is not a value of the type. */
    public Formula toValueFormula(int key, FormulaVar var) {
        final Object value = toValue(key, var);
        if (value == null) return null;
        final FormulaType<?> type = var.type();
        if (type.isBooleanType()) return bmgr.makeBoolean((Boolean) value);
        if (type.isIntegerType()) {
            return fmgr.getIntegerFormulaManager().makeNumber((BigInteger) value);
        }
        return fmgr.getBitvectorFormulaManager()
                .makeBitvector(((FormulaType.BitvectorType) type).getSize(), (BigInteger) value);
    }

    // ---- syntactic queries ----

    /**
     * A value that {@code formula} forces on {@code var} syntactically: an equality with a constant
     * (or the variable itself, or its negation, for booleans), alone or as a top-level conjunct.
     * Returns null if there is none.
     */
    public Determined findDeterminedValue(BooleanFormula formula, FormulaVar var) {
        final Determined direct = determinedBy(formula, var);
        if (direct != null) return direct;
        for (BooleanFormula conjunct : bmgr.toConjunctionArgs(formula, false)) {
            final Determined determined = determinedBy(conjunct, var);
            if (determined != null) return determined;
        }
        return null;
    }

    public record Determined(int key, Formula value) {}

    private Determined determinedBy(BooleanFormula formula, FormulaVar var) {
        if (var.type().isBooleanType()) {
            if (formula.equals(var.formula())) return new Determined(1, bmgr.makeTrue());
            if (formula.equals(bmgr.not((BooleanFormula) var.formula()))) {
                return new Determined(0, bmgr.makeFalse());
            }
        }
        return fmgr.visit(
                formula,
                new DefaultFormulaVisitor<>() {
                    @Override
                    protected Determined visitDefault(Formula f) {
                        return null;
                    }

                    @Override
                    public Determined visitFunction(
                            Formula f, List<Formula> args, FunctionDeclaration<?> decl) {
                        final FunctionDeclarationKind kind = decl.getKind();
                        if (args.size() != 2
                                || (kind != FunctionDeclarationKind.EQ
                                        && kind != FunctionDeclarationKind.BV_EQ
                                        && kind != FunctionDeclarationKind.IFF)) {
                            return null;
                        }
                        if (args.get(0).equals(var.formula())) return constant(args.get(1));
                        if (args.get(1).equals(var.formula())) return constant(args.get(0));
                        return null;
                    }

                    private Determined constant(Formula f) {
                        final Object value = constantValue(f);
                        return value == null ? null : new Determined(toKey(value, var), f);
                    }
                });
    }

    private Object constantValue(Formula formula) {
        return fmgr.visit(
                formula,
                new DefaultFormulaVisitor<>() {
                    @Override
                    protected Object visitDefault(Formula f) {
                        return null;
                    }

                    @Override
                    public Object visitConstant(Formula f, Object value) {
                        return value;
                    }
                });
    }
}
