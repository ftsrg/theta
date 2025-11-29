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

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.theta.analysis.algorithm.mdd.identitynode.IdentityRepresentation;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.model.BasicExprSubstitution;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.model.ExprSubstitution;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.utils.WithPushPop;
import java.util.function.Function;

public class MddExpressionTemplate implements MddNode.Template {

    private final Expr<BoolType> expr;
    private final Function<Object, Decl> extractDecl;
    private final SolverPool solverPool;
    private final boolean transExpr;
    private final boolean knownSat;

    private static Solver lazySolver;

    private static UnaryOperationCache<Expr<BoolType>, Boolean> satCache =
            new UnaryOperationCache();

    private static boolean isSat(Expr<BoolType> expr, SolverPool solverPool) {
        Boolean cached = satCache.getOrNull(expr);
        if (cached != null) {
            return cached;
        }
        if (lazySolver == null) lazySolver = solverPool.requestSolver();
        boolean res;
        try (var wpp = new WithPushPop(lazySolver)) {
            lazySolver.add(expr);
            res = lazySolver.check().isSat();
        }
        satCache.addToCache(expr, res);
        return res;
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

    @Override
    public RecursiveIntObjMapView<? extends MddNode> toCanonicalRepresentation(
            MddVariable mddVariable, MddCanonizationStrategy mddCanonizationStrategy) {
        final Decl decl = extractDecl.apply(mddVariable.getTraceInfo());

        final Expr<BoolType> canonizedExpr = ExprUtils.canonize(ExprUtils.simplify(expr));

        //        // TODO: we might not need this
        //        // Check if terminal 1
        //        if (ExprUtils.getConstants(canonizedExpr).isEmpty()) {
        //            if (canonizedExpr instanceof FalseExpr) {
        //                return mddVariable.getMddGraph().getTerminalZeroNode();
        //            } /*else {
        //                final MddGraph<Expr> mddGraph = (MddGraph<Expr>)
        // mddVariable.getMddGraph();
        //                return mddGraph.getNodeFor(canonizedExpr);
        //            }*/
        //        }

        // Check if terminal 0
        if (!knownSat
                && (canonizedExpr instanceof FalseExpr || !isSat(canonizedExpr, solverPool))) {
            return null;
        }

        // Check if default
        if (mddVariable.getDomainSize() == 0
                && !ExprUtils.getConstants(canonizedExpr).contains(decl)) {
            final MddNode childNode;
            if (mddVariable.getLower().isPresent()) {
                childNode =
                        mddVariable
                                .getLower()
                                .get()
                                .checkInNode(
                                        new MddExpressionTemplate(
                                                canonizedExpr,
                                                o -> (Decl) o,
                                                solverPool,
                                                transExpr,
                                                knownSat));
            } else {
                final MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();
                childNode = mddGraph.getNodeFor(canonizedExpr);
            }
            return MddExpressionRepresentation.ofDefault(
                    canonizedExpr, decl, mddVariable, solverPool, childNode, transExpr);
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
                    ExprUtils.simplify(overApproxSub.apply(canonizedExpr));

            boolean identityNeeded = false;

            if (!ExprUtils.getConstants(overApproxExpr).contains(decl)) {
                // If over and under mismatch then use solver to decide
                final var underConstants = ExprUtils.getConstants(underapproxExpr);
                if (underConstants.contains(decl) || underConstants.contains(nextDecl)) {
                    // Check if expr and not(x' = x) is sat
                    final var andExpr = And(expr, Neq(decl.getRef(), nextDecl.getRef()));
                    if (!isSat(andExpr, solverPool)) {
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
                                            new MddExpressionTemplate(
                                                    overApproxExpr,
                                                    extractDecl,
                                                    solverPool,
                                                    transExpr,
                                                    knownSat));
                } else {
                    final MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();
                    cont = mddGraph.getNodeFor(overApproxExpr);
                }
                return new IdentityRepresentation(cont);
            }
        }

        return MddExpressionRepresentation.of(
                canonizedExpr, decl, mddVariable, solverPool, transExpr);
    }
}
