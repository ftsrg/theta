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
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddCanonizationStrategy;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.UnaryOperationCache;
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation;
import java.util.Collections;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentMap;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;

/**
 * The JavaSMT counterpart of {@code MddExpressionTemplate}: checks a formula into an MDD level,
 * deciding whether it is empty, a level skip, an identity on a state variable, a single forced
 * value, or a node whose edges are enumerated lazily by the solver.
 */
public final class FormulaMddTemplate implements MddNode.Template {

    private final BooleanFormula formula;
    private final FormulaMddContext ctx;
    private final boolean transExpr;
    private final boolean knownSat;

    public static final MddGraph.Key<
                    UnaryOperationCache<BooleanFormula, Optional<Map<String, Object>>>>
            SAT_CACHE = new MddGraph.Key<>("formulaSatCache");

    // simplify outputs are fixed points: a memoized formula is not simplified again
    private static final MddGraph.Key<Set<BooleanFormula>> SIMPLIFIED =
            new MddGraph.Key<>("simplifiedFormulas");

    private static Set<BooleanFormula> newSimplifiedSet() {
        final ConcurrentMap<BooleanFormula, Boolean> weakIdentityMap =
                new MapMaker().weakKeys().makeMap();
        return Collections.newSetFromMap(weakIdentityMap);
    }

    static BooleanFormula simplify(
            final BooleanFormula formula, final FormulaMddContext ctx, final MddGraph<?> graph) {
        final Set<BooleanFormula> known =
                graph.getAttribute(SIMPLIFIED, FormulaMddTemplate::newSimplifiedSet);
        if (known.contains(formula)) {
            return formula;
        }
        final BooleanFormula result = ctx.simplify(formula);
        known.add(result);
        return result;
    }

    static BooleanFormula substituteAndSimplify(
            final BooleanFormula formula,
            final FormulaVar var,
            final Formula value,
            final FormulaMddContext ctx,
            final MddGraph<?> graph) {
        final Set<BooleanFormula> known =
                graph.getAttribute(SIMPLIFIED, FormulaMddTemplate::newSimplifiedSet);
        final BooleanFormula result = ctx.substituteAndSimplify(formula, var.formula(), value);
        known.add(result);
        return result;
    }

    static Map<String, Object> checkSat(
            BooleanFormula formula,
            FormulaMddContext ctx,
            UnaryOperationCache<BooleanFormula, Optional<Map<String, Object>>> satCache) {
        final Optional<Map<String, Object>> cached = satCache.getOrNull(formula);
        if (cached != null) {
            return cached.orElse(null);
        }
        final FormulaProverPool pool = ctx.getProverPool();
        final FormulaProver prover = pool.requestProver();
        final Map<String, Object> model;
        try {
            prover.push();
            try {
                prover.add(formula);
                model = prover.check() ? ctx.model(prover) : null;
            } finally {
                prover.pop();
            }
        } finally {
            pool.returnProver(prover);
        }
        satCache.addToCache(formula, Optional.ofNullable(model));
        return model;
    }

    private FormulaMddTemplate(
            BooleanFormula formula, FormulaMddContext ctx, boolean transExpr, boolean knownSat) {
        this.formula = formula;
        this.ctx = ctx;
        this.transExpr = transExpr;
        this.knownSat = knownSat;
    }

    public static FormulaMddTemplate of(BooleanFormula formula, FormulaMddContext ctx) {
        return new FormulaMddTemplate(formula, ctx, false, false);
    }

    public static FormulaMddTemplate of(
            BooleanFormula formula, FormulaMddContext ctx, boolean transExpr) {
        return new FormulaMddTemplate(formula, ctx, transExpr, false);
    }

    public static FormulaMddTemplate ofKnownSat(
            BooleanFormula formula, FormulaMddContext ctx, boolean transExpr) {
        return new FormulaMddTemplate(formula, ctx, transExpr, true);
    }

    private FormulaMddTemplate knownChild(BooleanFormula childFormula) {
        return ofKnownSat(childFormula, ctx, transExpr);
    }

    @SuppressWarnings("unchecked")
    private static MddGraph<BooleanFormula> graphOf(MddVariable mddVariable) {
        return (MddGraph<BooleanFormula>) mddVariable.getMddGraph();
    }

    @Override
    public RecursiveIntObjMapView<? extends MddNode> toCanonicalRepresentation(
            MddVariable mddVariable, MddCanonizationStrategy mddCanonizationStrategy) {
        final FormulaVar var = (FormulaVar) mddVariable.getTraceInfo();
        final MddGraph<BooleanFormula> graph = graphOf(mddVariable);
        final var satCache = graph.getAttribute(SAT_CACHE, UnaryOperationCache::new);
        final BooleanFormulaManager bmgr = ctx.getBooleanFormulaManager();

        final BooleanFormula simplified = simplify(formula, ctx, graph);

        // Check if terminal 0
        final Map<String, Object> satModel;
        if (knownSat) {
            satModel = null;
        } else if (ctx.isFalse(simplified)) {
            return null;
        } else {
            satModel = checkSat(simplified, ctx, satCache);
            if (satModel == null) return null;
        }

        // Check if default
        if (mddVariable.getDomainSize() == 0 && !ctx.contains(simplified, var)) {
            final MddNode childNode;
            if (mddVariable.getLower().isPresent()) {
                childNode = mddVariable.getLower().get().checkInNode(knownChild(simplified));
            } else {
                childNode = graph.getNodeFor(simplified);
            }
            return FormulaMddRepresentation.ofDefault(
                    simplified, var, mddVariable, ctx, childNode, transExpr);
        }

        if (transExpr && !var.next() && mddVariable.getLower().isPresent()) {

            final FormulaVar nextVar = (FormulaVar) mddVariable.getLower().get().getTraceInfo();

            // Overapproximate by replacing x' with x everywhere
            final BooleanFormula overApprox =
                    simplify(
                            ctx.substitute(simplified, Map.of(nextVar.formula(), var.formula())),
                            ctx,
                            graph);

            // The solver decides: replacing x' = x atoms with false is no proof, as the
            // simplifier may rewrite x' = not x into not (x' = x)
            final boolean identityNeeded =
                    !ctx.contains(overApprox, var)
                            && checkSat(
                                            bmgr.and(
                                                    formula,
                                                    bmgr.not(ctx.equal(var, nextVar.formula()))),
                                            ctx,
                                            satCache)
                                    == null;

            if (identityNeeded) {
                final MddNode cont;
                if (mddVariable.getLower().get().getLower().isPresent()) {
                    cont =
                            mddVariable
                                    .getLower()
                                    .get()
                                    .getLower()
                                    .get()
                                    .checkInNode(knownChild(overApprox));
                } else {
                    cont = graph.getNodeFor(overApprox);
                }
                return new IdentityRepresentation(cont);
            }
        }

        final FormulaMddContext.Determined determined = ctx.findDeterminedValue(simplified, var);
        if (determined != null) {
            final BooleanFormula substituted =
                    substituteAndSimplify(simplified, var, determined.value(), ctx, graph);

            final MddNode childNode;
            if (mddVariable.getLower().isPresent()) {
                childNode = mddVariable.getLower().get().checkInNode(knownChild(substituted));
            } else {
                childNode = graph.getNodeFor(substituted);
            }

            return FormulaMddRepresentation.ofDetermined(
                    simplified, var, mddVariable, ctx, determined.key(), childNode, transExpr);
        }

        return FormulaMddRepresentation.of(simplified, var, mddVariable, ctx, transExpr, satModel);
    }
}
