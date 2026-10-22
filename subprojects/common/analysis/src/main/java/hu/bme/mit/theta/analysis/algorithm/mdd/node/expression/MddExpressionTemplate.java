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
package hu.bme.mit.theta.analysis.algorithm.mdd.node.expression;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import com.google.common.collect.MapMaker;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.theta.analysis.algorithm.mdd.node.identity.IdentityRepresentation;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.model.BasicExprSubstitution;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.model.ExprSubstitution;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentMap;
import java.util.function.Function;

public class MddExpressionTemplate implements MddNode.Template {

    private final Expr<BoolType> expr;
    private final Function<Object, Decl> extractDecl;
    private final SolverPool solverPool;
    private final boolean transExpr;
    private final boolean knownSat;

    public static final MddGraph.Key<UnaryOperationCache<Expr<BoolType>, Optional<Valuation>>>
            SAT_CACHE = new MddGraph.Key<>("satCache");

    // simplify outputs are fixed points: a memoized expression is not simplified again
    private static final MddGraph.Key<Set<Expr<BoolType>>> SIMPLIFIED =
            new MddGraph.Key<>("simplifiedExprs");

    private static Set<Expr<BoolType>> newSimplifiedSet() {
        final ConcurrentMap<Expr<BoolType>, Boolean> weakIdentityMap =
                new MapMaker().weakKeys().makeMap();
        return Collections.newSetFromMap(weakIdentityMap);
    }

    static Expr<BoolType> simplify(final Expr<BoolType> expr, final MddGraph<?> graph) {
        final Set<Expr<BoolType>> known =
                graph.getAttribute(SIMPLIFIED, MddExpressionTemplate::newSimplifiedSet);
        if (known.contains(expr)) {
            return expr;
        }
        final Expr<BoolType> result = ExprUtils.simplify(expr);
        known.add(result);
        return result;
    }

    static Expr<BoolType> simplify(
            final Expr<BoolType> expr, final Valuation valuation, final MddGraph<?> graph) {
        final Set<Expr<BoolType>> known =
                graph.getAttribute(SIMPLIFIED, MddExpressionTemplate::newSimplifiedSet);
        final Expr<BoolType> result = ExprUtils.simplify(expr, valuation);
        known.add(result);
        return result;
    }

    /** Substitutes a key's value, a literal or a term over symbols, for {@code decl}. */
    static Expr<BoolType> simplify(
            final Expr<BoolType> expr,
            final Decl<?> decl,
            final Expr<?> value,
            final MddGraph<?> graph) {
        if (value instanceof LitExpr<?> lit) {
            return simplify(expr, ImmutableValuation.builder().put(decl, lit).build(), graph);
        }
        final Set<Expr<BoolType>> known =
                graph.getAttribute(SIMPLIFIED, MddExpressionTemplate::newSimplifiedSet);
        final Expr<BoolType> result =
                ExprUtils.simplify(
                        BasicSubstitution.builder().put(decl, value).build().apply(expr));
        known.add(result);
        return result;
    }

    private static Valuation checkSat(
            Expr<BoolType> expr,
            SolverPool solverPool,
            UnaryOperationCache<Expr<BoolType>, Optional<Valuation>> satCache) {
        Optional<Valuation> cached = satCache.getOrNull(expr);
        if (cached != null) {
            return cached.orElse(null);
        }
        final var solver = solverPool.requestSolver();
        final Valuation model;
        try (var wpp = new WithPushPop(solver)) {
            solver.add(expr);
            model = solver.check().isSat() ? solver.getModel() : null;
        } finally {
            solverPool.returnSolver(solver);
        }
        satCache.addToCache(expr, Optional.ofNullable(model));
        return model;
    }

    private MddExpressionTemplate(
            Expr<BoolType> expr,
            Function<Object, Decl> extractDecl,
            SolverPool solverPool,
            boolean transExpr,
            boolean knownSat) {
        this.expr = expr;
        this.extractDecl = extractDecl;
        this.solverPool = solverPool;
        this.transExpr = transExpr;
        this.knownSat = knownSat;
    }

    public static MddExpressionTemplate of(
            Expr<BoolType> expr, Function<Object, Decl> extractDecl, SolverPool solverPool) {
        return new MddExpressionTemplate(expr, extractDecl, solverPool, false, false);
    }

    public static MddExpressionTemplate of(
            Expr<BoolType> expr,
            Function<Object, Decl> extractDecl,
            SolverPool solverPool,
            boolean transExpr) {
        return new MddExpressionTemplate(expr, extractDecl, solverPool, transExpr, false);
    }

    public static MddExpressionTemplate ofKnownSat(
            Expr<BoolType> expr,
            Function<Object, Decl> extractDecl,
            SolverPool solverPool,
            boolean transExpr) {
        return new MddExpressionTemplate(expr, extractDecl, solverPool, transExpr, true);
    }

    private MddExpressionTemplate knownChild(Expr<BoolType> childExpr) {
        return ofKnownSat(childExpr, o -> (Decl) o, solverPool, transExpr);
    }

    @Override
    public RecursiveIntObjMapView<? extends MddNode> toCanonicalRepresentation(
            MddVariable mddVariable, MddCanonizationStrategy mddCanonizationStrategy) {
        final Decl decl = extractDecl.apply(mddVariable.getTraceInfo());
        final var satCache =
                mddVariable.getMddGraph().getAttribute(SAT_CACHE, UnaryOperationCache::new);

        final Expr<BoolType> simplifiedExpr = simplify(expr, mddVariable.getMddGraph());

        // Check if terminal 0
        final Valuation satModel;
        if (knownSat) {
            satModel = null;
        } else if (simplifiedExpr instanceof FalseExpr) {
            return null;
        } else {
            satModel = checkSat(ExprUtils.canonize(simplifiedExpr), solverPool, satCache);
            if (satModel == null) return null;
        }

        // Check if default
        if (mddVariable.getDomainSize() == 0
                && !ExprUtils.getConstants(simplifiedExpr).contains(decl)) {
            final MddNode childNode;
            if (mddVariable.getLower().isPresent()) {
                childNode = mddVariable.getLower().get().checkInNode(knownChild(simplifiedExpr));
            } else {
                final MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();
                childNode = terminalFor(mddGraph, simplifiedExpr, simplifiedExpr);
            }
            return MddExpressionRepresentation.ofDefault(
                    simplifiedExpr, decl, mddVariable, solverPool, childNode, transExpr);
        }

        if (transExpr
                && decl instanceof IndexedConstDecl<?> constDecl
                && constDecl.getIndex() == 0) {

            // Distinction between under- and overapproximation is needed because of formulas like
            // x' = x or x' = 4, where simplify can overapproximate

            // First underapproximate by replacing x' = x with false (and also x = x')
            final var nextDecl = extractDecl.apply(mddVariable.getLower().get().getTraceInfo());
            final ExprSubstitution underApproxSub =
                    new BasicExprSubstitution.Builder()
                            .put(Eq(nextDecl.getRef(), decl.getRef()), False())
                            .put(Eq(decl.getRef(), nextDecl.getRef()), False())
                            .build();
            final Expr<BoolType> underapproxExpr = underApproxSub.apply(expr);

            // Then overapproximate by replacing x' with x everywhere
            final Substitution overApproxSub =
                    BasicSubstitution.builder()
                            .put(
                                    extractDecl.apply(mddVariable.getLower().get().getTraceInfo()),
                                    decl.getRef())
                            .build();
            final Expr<BoolType> overApproxExpr =
                    simplify(overApproxSub.apply(simplifiedExpr), mddVariable.getMddGraph());

            boolean identityNeeded = false;

            if (!ExprUtils.getConstants(overApproxExpr).contains(decl)) {
                // If over and under mismatch then use solver to decide
                final var underConstants = ExprUtils.getConstants(underapproxExpr);
                if (underConstants.contains(decl) || underConstants.contains(nextDecl)) {
                    // Check if expr and not(x' = x) is sat
                    final var andExpr = And(expr, Neq(decl.getRef(), nextDecl.getRef()));
                    if (checkSat(andExpr, solverPool, satCache) == null) {
                        identityNeeded = true;
                    }
                } else {
                    identityNeeded = true;
                }
            }

            if (identityNeeded) {
                final MddNode cont;
                if (mddVariable.getLower().isPresent()
                        && mddVariable.getLower().get().getLower().isPresent()) {
                    cont =
                            mddVariable
                                    .getLower()
                                    .get()
                                    .getLower()
                                    .get()
                                    .checkInNode(
                                            MddExpressionTemplate.ofKnownSat(
                                                    overApproxExpr,
                                                    extractDecl,
                                                    solverPool,
                                                    transExpr));
                } else {
                    final MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();
                    cont = terminalFor(mddGraph, overApproxExpr, overApproxExpr);
                }
                return new IdentityRepresentation(cont);
            }
        }

        final Expr<?> determinedValue =
                findDeterminedValue(simplifiedExpr, decl, isNextState(decl));
        if (determinedValue != null) {
            final int key = LitExprConverter.toInt(determinedValue);

            final Expr<BoolType> substitutedExpr =
                    simplify(simplifiedExpr, decl, determinedValue, mddVariable.getMddGraph());

            final MddNode childNode;
            if (mddVariable.getLower().isPresent()) {
                childNode = mddVariable.getLower().get().checkInNode(knownChild(substitutedExpr));
            } else {
                final MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();
                childNode = terminalFor(mddGraph, substitutedExpr, substitutedExpr);
            }

            return MddExpressionRepresentation.ofDetermined(
                    simplifiedExpr, decl, mddVariable, solverPool, key, childNode, transExpr);
        }

        return MddExpressionRepresentation.of(
                simplifiedExpr, decl, mddVariable, solverPool, transExpr, satModel);
    }

    // a term can only be the key of a next-state level: source levels are matched against the
    // keys of the states, so a term there would hide every concrete source
    private boolean isNextState(Decl<?> decl) {
        return LitExprConverter.isSymbolic()
                && transExpr
                && decl instanceof IndexedConstDecl<?> constDecl
                && constDecl.getIndex() > 0;
    }

    private static Expr<?> findDeterminedValue(Expr<BoolType> expr, Decl<?> decl, boolean terms) {
        if (expr instanceof EqExpr<?> eq) {
            return extractLiteralForDecl(eq, decl, terms);
        }
        if (expr instanceof AndExpr and) {
            for (var op : and.getOps()) {
                if (op instanceof EqExpr<?> eq) {
                    final Expr<?> lit = extractLiteralForDecl(eq, decl, terms);
                    if (lit != null) return lit;
                }
            }
        }
        return null;
    }

    private static Expr<?> extractLiteralForDecl(EqExpr<?> eq, Decl<?> decl, boolean terms) {
        if (eq.getLeftOp() instanceof RefExpr<?> ref
                && ref.getDecl().equals(decl)
                && isValue(eq.getRightOp(), terms)) {
            return eq.getRightOp();
        }
        if (eq.getRightOp() instanceof RefExpr<?> ref
                && ref.getDecl().equals(decl)
                && isValue(eq.getLeftOp(), terms)) {
            return eq.getLeftOp();
        }
        return null;
    }

    /**
     * The terminal for a satisfiable residual; in symbolic mode it keeps what the residual says
     * about symbols, otherwise it is {@code otherwise}.
     */
    @SuppressWarnings("unchecked")
    static MddNode terminalFor(
            MddGraph<?> graph, Expr<BoolType> residual, Expr<BoolType> otherwise) {
        final MddGraph<Expr> mddGraph = (MddGraph<Expr>) graph;
        if (!LitExprConverter.isSymbolic()) return mddGraph.getNodeFor(otherwise);
        final Expr<BoolType> projected =
                ExprUtils.canonize(SymbolicKeys.withoutIntermediates(residual));
        return mddGraph.getNodeFor(
                ExprUtils.getConstants(projected).isEmpty() ? True() : projected);
    }

    // where terms are allowed, a non-bool term over symbols only (no level decls) is a value
    private static boolean isValue(Expr<?> expr, boolean terms) {
        if (expr instanceof LitExpr<?>) return true;
        return terms
                && !(expr.getType() instanceof BoolType)
                && ExprUtils.getConstants(expr).stream()
                        .noneMatch(c -> c instanceof IndexedConstDecl<?>);
    }
}
