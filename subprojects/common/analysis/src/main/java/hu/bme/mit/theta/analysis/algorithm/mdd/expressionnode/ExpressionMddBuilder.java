/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mdd.expressionnode;

import com.google.common.base.Preconditions;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.MddGraph;
import hu.bme.mit.delta.java.mdd.MddNode;
import hu.bme.mit.delta.java.mdd.MddVariable;
import hu.bme.mit.delta.java.mdd.UnaryOperationCache;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

public class ExpressionMddBuilder {

    private final Map<MddExpressionRepresentation, Solver> solvers;
    private final SolverPool solverPool;

    private final Solver globalSolver;
    private static UnaryOperationCache<Expr<BoolType>, Valuation> valuationCache = new UnaryOperationCache<>();

    public SolverPool getSolverPool() {
        return solverPool;
    }

    public ExpressionMddBuilder(SolverPool solverPool) {
        this.solvers = new LinkedHashMap<>();
        this.solverPool = solverPool;
        this.globalSolver = solverPool.requestSolver();
    }

    public MddNode createNode(Expr<BoolType> expr, MddVariable variable, boolean transExpr) {

        final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(expr);

        // Check if terminal 0
        if (simplifiedExpr instanceof FalseExpr) {
            return null;
        }

        // Check if cached
        var cached = valuationCache.getOrNull(simplifiedExpr);
        if (cached != null) {
            return cached.equals(ExplState.bottom()) ? null : createNodeNonNull(simplifiedExpr, variable, transExpr);
        }

        // Run solver and cache result
        try (var wpp = new WithPushPop(globalSolver)) {
            globalSolver.add(simplifiedExpr);
            final boolean res = globalSolver.check().isSat();
            if (res) {
                final var model = globalSolver.getModel();
                valuationCache.addToCache(simplifiedExpr, model);
                final var node = createNodeNonNull(simplifiedExpr, variable, transExpr);
                cacheModel(node, globalSolver.getModel());
                return node;
            } else {
                valuationCache.addToCache(simplifiedExpr, ExplState.bottom());
                return null;
            }
        }

    }

    public MddNode createTerminal(Expr<BoolType> expr, MddGraph<Expr> mddGraph) {

        final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(expr);

        // Check if terminal 0
        if (simplifiedExpr instanceof FalseExpr) {
            return null;
        }

        // Check if cached
        var cached = valuationCache.getOrNull(simplifiedExpr);
        if (cached != null) {
            return cached.equals(ExplState.bottom()) ? null : createTerminalNonNull(simplifiedExpr, mddGraph);
        }

        // Run solver and cache result
        try (var wpp = new WithPushPop(globalSolver)) {
            globalSolver.add(simplifiedExpr);
            final boolean res = globalSolver.check().isSat();
            if (res) {
                final var model = globalSolver.getModel();
                valuationCache.addToCache(simplifiedExpr, model);
                final var node = createTerminalNonNull(simplifiedExpr, mddGraph);
                cacheModel(node, globalSolver.getModel());
                return node;
            } else {
                valuationCache.addToCache(simplifiedExpr, ExplState.bottom());
                return null;
            }
        }
    }

    private MddNode createNodeNonNull(Expr<BoolType> expr, MddVariable variable, boolean transExpr) {
        return variable.checkInNode(MddExpressionTemplate.of(expr, o -> (Decl) o, solverPool, transExpr));
    }

    private MddNode createTerminalNonNull(Expr<BoolType> expr, MddGraph<Expr> mddGraph) {
        return mddGraph.getNodeFor(expr);
    }

    public void cacheModel(MddNode node, Valuation valuation) {
        if(node.isTerminal()) return;
        cacheModel(node.getRepresentation(), valuation);
    }

    public void cacheModel(RecursiveIntObjMapView<? extends MddNode> representation, Valuation valuation) {
        Preconditions.checkArgument(!valuation.equals(ExplState.bottom()));
        if (representation instanceof IdentityExpressionRepresentation identityExpressionRepresentation){
            cacheModel(identityExpressionRepresentation.getContinuation(), valuation);
        }
        if (representation instanceof MddExpressionRepresentation expressionRepresentation) {
            // Level skip
            if (expressionRepresentation.getExplicitRepresentation().getCacheView().defaultValue() != null) {
                cacheModel(expressionRepresentation.getExplicitRepresentation().getCacheView().defaultValue(), valuation);
            }

            // Create substituted expr
            final Optional<? extends LitExpr<?>> literal =
                    valuation.eval(expressionRepresentation.getDecl());
            final Expr<BoolType> substitutedExpr = literal.isPresent() ?
                    ExprUtils.simplify(expressionRepresentation.getExpr(),ImmutableValuation.builder().put(expressionRepresentation.getDecl(), literal.get()).build())
                    : expressionRepresentation.getExpr();

            if (literal.isPresent()
                    && expressionRepresentation
                    .getExplicitRepresentation()
                    .getCacheView()
                    .containsKey(LitExprConverter.toInt(literal.get()))) {
                // If node is already stored
                cacheModel(expressionRepresentation
                                .getExplicitRepresentation()
                                .getCacheView()
                                .get(LitExprConverter.toInt(literal.get())), valuation);
            } else {
                // Create new node (terminal or not)
                final MddNode newNode;
                final Optional<? extends MddVariable> lower =
                        expressionRepresentation.getMddVariable().getLower();
                if (lower.isPresent()) {
                    newNode = createNodeNonNull(substitutedExpr, lower.get(), expressionRepresentation.isTransExpr());
                } else {
                    newNode = createTerminalNonNull(substitutedExpr, (MddGraph<Expr>) expressionRepresentation.getMddVariable().getMddGraph());
                }

                assert !expressionRepresentation.getMddVariable().isNullOrZero(newNode)
                        : "This would mean the model returned by the solver is incorrect";

                // TODO update domainSize
                if (literal.isPresent())
                    expressionRepresentation.getExplicitRepresentation().cacheNode(
                            LitExprConverter.toInt(literal.get()), newNode);
                cacheModel(newNode, valuation);

            }

        }

    }

    public MddNode queryEdge(MddExpressionRepresentation representation, int assignment) {
        final var cached = representation.getExplicitRepresentation().getCacheView().get(assignment);
        if (cached != null || representation.getExplicitRepresentation().isComplete())
            return cached;
        // TODO: this way null values are never cached and have to be recomputed every time

        final var mddVariable = representation.getMddVariable();
        final var decl = representation.getDecl();

        final MutableValuation val = new MutableValuation();
        final LitExpr<?> litExpr = LitExprConverter.toLitExpr(assignment, decl.getType());
        if (litExpr.isInvalid()) {
            return null;
        }

        val.put(decl, litExpr);
        final Expr<BoolType> simplifiedExpr = ExprUtils.simplify(representation.getExpr(), val);

        final MddNode childNode;
        if (mddVariable.getLower().isPresent()) {
            childNode = createNode(simplifiedExpr, mddVariable.getLower().get(), representation.isTransExpr());
        } else {
            childNode = createTerminal(simplifiedExpr, (MddGraph<Expr>) mddVariable.getMddGraph());
        }

        if (!mddVariable.isNullOrZero(childNode))
            representation.getExplicitRepresentation().cacheNode(assignment, childNode);
        return childNode;
    }
}
