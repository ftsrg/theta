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
package hu.bme.mit.theta.vmt;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.sosy_lab.java_smt.api.BitvectorFormula;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.FunctionDeclaration;
import org.sosy_lab.java_smt.api.FunctionDeclarationKind;
import org.sosy_lab.java_smt.api.NumeralFormula;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;
import org.sosy_lab.java_smt.api.visitors.FormulaTransformationVisitor;

/**
 * Replaces uninterpreted function applications by frozen state variables, so a function keeps its
 * interpretation along a run instead of being chosen anew in every step.
 *
 * <p>The function values are chosen once, in an extra first step: the run starts in a pre-state
 * where the frozen variables hold a fixed default, so the initial states stay finite. Properties
 * are only checked after the choice, and a trace has this extra step at its start.
 *
 * <p>Each argument value tuple of a function gets one frozen variable. An application whose
 * arguments are constants becomes that variable; one with non-constant arguments becomes an
 * if-then-else over all value tuples, which needs every non-constant argument to have a finite sort
 * (Bool or a bit-vector), with at most {@value #MAX_TUPLES} tuples per application.
 */
final class UfElimination {

    static final int MAX_TUPLES = 4096;
    private static final String PREFIX = "__uf_";

    private final FormulaManager fmgr;
    private final BooleanFormulaManager bmgr;
    private final Map<String, VmtStateVar> frozen = new LinkedHashMap<>();
    private final java.util.Set<String> usedNames = new java.util.HashSet<>();

    private UfElimination(FormulaManager fmgr) {
        this.fmgr = fmgr;
        this.bmgr = fmgr.getBooleanFormulaManager();
    }

    static VmtModel apply(VmtModel model) {
        final FormulaManager fmgr = model.getFormulaManager();
        final BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();
        final UfElimination elimination = new UfElimination(fmgr);
        final BooleanFormula init = elimination.eliminate(model.getInit());
        final List<BooleanFormula> split = new ArrayList<>();
        for (BooleanFormula part : model.getTransSplit()) split.add(elimination.eliminate(part));
        final List<BooleanFormula> props = new ArrayList<>();
        for (VmtProperty p : model.getProperties()) props.add(elimination.eliminate(p.formula()));
        if (elimination.frozen.isEmpty()) return model;

        final String readyName = elimination.freshName(PREFIX + "ready");
        final BooleanFormula ready = bmgr.makeVariable(readyName);
        final BooleanFormula readyNext = bmgr.makeVariable(readyName + ".next");

        // pre-state: not ready, frozen variables at a fixed default, the model's variables in a
        // state allowed by init for some function values (fresh inputs stand for those values)
        final List<BooleanFormula> preState = new ArrayList<>(List.of(bmgr.not(ready)));
        final Map<Formula, Formula> toInitInputs = new LinkedHashMap<>();
        final Map<Formula, Formula> toNext = new LinkedHashMap<>();
        final List<Formula> inputVars = new ArrayList<>(model.getInputVars());
        final List<BooleanFormula> keep = new ArrayList<>();
        for (VmtStateVar v : elimination.frozen.values()) {
            preState.add(
                    elimination.equal(v.current(), elimination.defaultValue(v.type()), v.type()));
            final String inputName = elimination.freshName(v.name() + "_init");
            final Formula input = fmgr.makeVariable(v.type(), inputName);
            inputVars.add(input);
            toInitInputs.put(v.current(), input);
            toNext.put(v.current(), v.next());
            keep.add(elimination.equal(v.next(), v.current(), v.type()));
        }
        preState.add(fmgr.substitute(init, toInitInputs));

        // choice step: fix the function values once, consistently with init, and stutter
        final List<BooleanFormula> choice =
                new ArrayList<>(List.of(bmgr.not(ready), readyNext, fmgr.substitute(init, toNext)));
        for (VmtStateVar v : model.getStateVars()) {
            choice.add(elimination.equal(v.next(), v.current(), v.type()));
        }
        // the chosen value is named by an input, not left free: a free next-state value would
        // become an unbounded default edge in the MDD
        for (VmtStateVar v : elimination.frozen.values()) {
            final Formula chosen =
                    fmgr.makeVariable(v.type(), elimination.freshName(v.name() + "_choice"));
            inputVars.add(chosen);
            choice.add(
                    elimination.equal(v.current(), elimination.defaultValue(v.type()), v.type()));
            choice.add(elimination.equal(v.next(), chosen, v.type()));
        }

        // every original disjunct runs once ready and keeps the function values
        final List<BooleanFormula> parts = new ArrayList<>(List.of(bmgr.and(choice)));
        for (BooleanFormula part : split) {
            parts.add(bmgr.and(part, ready, readyNext, bmgr.and(keep)));
        }

        final List<VmtProperty> properties = new ArrayList<>();
        for (int k = 0; k < props.size(); k++) {
            final VmtProperty p = model.getProperties().get(k);
            properties.add(
                    new VmtProperty(
                            p.kind(), p.index(), p.name(), bmgr.implication(ready, props.get(k))));
        }

        final List<VmtStateVar> stateVars = new ArrayList<>(model.getStateVars());
        stateVars.add(
                new VmtStateVar(
                        readyName,
                        ready,
                        readyName + ".next",
                        readyNext,
                        FormulaType.BooleanType,
                        false));
        stateVars.addAll(elimination.frozen.values());
        return new VmtModel(
                fmgr, stateVars, inputVars, bmgr.and(preState), bmgr.or(parts), properties);
    }

    private String freshName(String base) {
        String name = base;
        while (!usedNames.add(name)) name = name + "_";
        return name;
    }

    private Formula defaultValue(FormulaType<?> type) {
        if (type.isBooleanType()) return bmgr.makeFalse();
        if (type.isIntegerType()) return fmgr.getIntegerFormulaManager().makeNumber(0);
        if (type.isRationalType()) return fmgr.getRationalFormulaManager().makeNumber(0);
        if (type.isBitvectorType()) {
            return fmgr.getBitvectorFormulaManager()
                    .makeBitvector(((FormulaType.BitvectorType) type).getSize(), 0);
        }
        throw new VmtParseException("Unsupported uninterpreted function sort " + type);
    }

    private BooleanFormula eliminate(BooleanFormula formula) {
        return fmgr.transformRecursively(
                formula,
                new FormulaTransformationVisitor(fmgr) {
                    @Override
                    public Formula visitFunction(
                            Formula f, List<Formula> newArgs, FunctionDeclaration<?> decl) {
                        if (decl.getKind() == FunctionDeclarationKind.UF && !newArgs.isEmpty()) {
                            return replace(decl, newArgs);
                        }
                        return super.visitFunction(f, newArgs, decl);
                    }
                });
    }

    private Formula replace(FunctionDeclaration<?> decl, List<Formula> args) {
        // the candidate values of each argument: its constant value, or all values of its sort
        final List<List<Object>> candidates = new ArrayList<>();
        long tuples = 1;
        for (int i = 0; i < args.size(); i++) {
            final Formula arg = args.get(i);
            final Object constant =
                    fmgr.extractVariablesAndUFs(arg).isEmpty() ? constantValue(arg) : null;
            if (constant != null) {
                candidates.add(List.of(constant));
            } else {
                final List<Object> values = allValues(decl.getArgumentTypes().get(i), decl, arg);
                candidates.add(values);
                tuples *= values.size();
                if (tuples > MAX_TUPLES) {
                    throw new VmtParseException(
                            "Uninterpreted function "
                                    + decl.getName()
                                    + " is applied to more than "
                                    + MAX_TUPLES
                                    + " argument values in "
                                    + decl.getName()
                                    + args);
                }
            }
        }

        final List<List<Object>> allTuples = new ArrayList<>();
        product(candidates, 0, new ArrayList<>(), allTuples);
        Formula result = null;
        for (List<Object> tuple : allTuples) {
            final Formula value = frozenVar(decl, tuple).current();
            if (result == null) {
                result = value;
                continue;
            }
            final List<BooleanFormula> matches = new ArrayList<>();
            for (int i = 0; i < args.size(); i++) {
                if (candidates.get(i).size() > 1) {
                    final FormulaType<?> type = decl.getArgumentTypes().get(i);
                    matches.add(equal(args.get(i), valueFormula(tuple.get(i), type), type));
                }
            }
            result = bmgr.ifThenElse(bmgr.and(matches), value, result);
        }
        return result;
    }

    private VmtStateVar frozenVar(FunctionDeclaration<?> decl, List<Object> tuple) {
        final String key = decl.getName() + tuple;
        return frozen.computeIfAbsent(
                key,
                k -> {
                    final String name =
                            freshName(
                                    (PREFIX + decl.getName() + "_" + tuple)
                                            .replaceAll("[^A-Za-z0-9_]", "_"));
                    final FormulaType<?> type = decl.getType();
                    return new VmtStateVar(
                            name,
                            fmgr.makeVariable(type, name),
                            name + ".next",
                            fmgr.makeVariable(type, name + ".next"),
                            type,
                            true);
                });
    }

    private List<Object> allValues(FormulaType<?> type, FunctionDeclaration<?> decl, Formula arg) {
        if (type.isBooleanType()) return List.of(false, true);
        if (type.isBitvectorType()) {
            final int size = ((FormulaType.BitvectorType) type).getSize();
            if (size < 31 && (1L << size) <= MAX_TUPLES) {
                final List<Object> values = new ArrayList<>();
                for (long v = 0; v < (1L << size); v++) values.add(BigInteger.valueOf(v));
                return values;
            }
        }
        throw new VmtParseException(
                "Uninterpreted function "
                        + decl.getName()
                        + " is applied to the non-constant argument "
                        + arg
                        + " of sort "
                        + type
                        + "; only Bool and small bit-vector arguments can be enumerated");
    }

    private static void product(
            List<List<Object>> candidates,
            int index,
            List<Object> prefix,
            List<List<Object>> result) {
        if (index == candidates.size()) {
            result.add(List.copyOf(prefix));
            return;
        }
        for (Object value : candidates.get(index)) {
            prefix.add(value);
            product(candidates, index + 1, prefix, result);
            prefix.remove(prefix.size() - 1);
        }
    }

    private Object constantValue(Formula formula) {
        final Formula simplified;
        try {
            simplified = fmgr.simplify(formula);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException(e);
        }
        return fmgr.visit(
                simplified,
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

    private Formula valueFormula(Object value, FormulaType<?> type) {
        if (type.isBooleanType()) return bmgr.makeBoolean((Boolean) value);
        if (type.isBitvectorType()) {
            return fmgr.getBitvectorFormulaManager()
                    .makeBitvector(
                            ((FormulaType.BitvectorType) type).getSize(), (BigInteger) value);
        }
        throw new IllegalArgumentException("Cannot enumerate sort " + type);
    }

    @SuppressWarnings("unchecked")
    private BooleanFormula equal(Formula a, Formula b, FormulaType<?> type) {
        if (type.isBooleanType()) {
            return bmgr.equivalence((BooleanFormula) a, (BooleanFormula) b);
        }
        if (type.isIntegerType()) {
            return fmgr.getIntegerFormulaManager().equal((IntegerFormula) a, (IntegerFormula) b);
        }
        if (type.isRationalType()) {
            return fmgr.getRationalFormulaManager().equal((NumeralFormula) a, (NumeralFormula) b);
        }
        if (type.isBitvectorType()) {
            return fmgr.getBitvectorFormulaManager()
                    .equal((BitvectorFormula) a, (BitvectorFormula) b);
        }
        throw new VmtParseException("Unsupported uninterpreted function sort " + type);
    }
}
