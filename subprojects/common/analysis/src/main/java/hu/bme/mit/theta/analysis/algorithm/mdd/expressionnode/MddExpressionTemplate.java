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

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.collections.RecursiveIntObjMapView;
import hu.bme.mit.delta.java.mdd.*;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.model.BasicSubstitution;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverPool;
import hu.bme.mit.theta.solver.utils.WithPushPop;

import java.util.Optional;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

public class MddExpressionTemplate implements MddNode.Template {

    private final Expr<BoolType> expr;

    private final Function<Object, Decl> extractDecl;
    private final ExpressionMddBuilder expressionMddBuilder;


    private final boolean transExpr;

    private MddExpressionTemplate(
            Expr<BoolType> expr, Function<Object, Decl> extractDecl, ExpressionMddBuilder expressionMddBuilder, boolean transExpr) {
        this.expr = expr;
        this.extractDecl = extractDecl;
        this.expressionMddBuilder = expressionMddBuilder;
        this.transExpr = transExpr;
    }

    public static MddNode.Template of(
            Expr<BoolType> expr, Function<Object, Decl> extractDecl, ExpressionMddBuilder expressionMddBuilder) {
        return MddExpressionTemplate.of(expr, extractDecl, expressionMddBuilder, false);
    }

    public static MddExpressionTemplate of(
            Expr<BoolType> expr, Function<Object, Decl> extractDecl, ExpressionMddBuilder expressionMddBuilder, boolean transExpr) {
        return new MddExpressionTemplate(expr, extractDecl, expressionMddBuilder, transExpr);
    }

    @Override
    public RecursiveIntObjMapView<? extends MddNode> toCanonicalRepresentation(
            MddVariable mddVariable, MddCanonizationStrategy mddCanonizationStrategy) {
        final Decl decl = extractDecl.apply(mddVariable.getTraceInfo());

        final Expr<BoolType> canonizedExpr = ExprUtils.canonize(ExprUtils.simplify(expr));

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
                                                canonizedExpr, o -> (Decl) o, expressionMddBuilder, transExpr));
            } else {
                final MddGraph<Expr> mddGraph = (MddGraph<Expr>) mddVariable.getMddGraph();
                childNode = mddGraph.getNodeFor(canonizedExpr);
            }
            return MddExpressionRepresentation.ofDefault(
                    canonizedExpr, decl, mddVariable, expressionMddBuilder, childNode, transExpr);
        }

        if (transExpr && decl instanceof IndexedConstDecl<?> constDecl && constDecl.getIndex() == 0 && mddVariable.getLower().isPresent() && mddVariable.getLower().get().getLower().isPresent()) {
            final Substitution sub =
                    BasicSubstitution.builder().put(extractDecl.apply(mddVariable.getLower().get().getTraceInfo()), decl.getRef()).build();
            final Expr<BoolType> identityContinuationExpr = ExprUtils.simplify(sub.apply(canonizedExpr));
            if (!ExprUtils.getConstants(identityContinuationExpr).contains(decl)) {
                final var cont = mddVariable.getLower().get().getLower().get().checkInNode(
                        new MddExpressionTemplate(identityContinuationExpr, extractDecl, expressionMddBuilder, transExpr)
                );
                return new IdentityExpressionRepresentation(cont);
            }
        }

        final var newRepresentation = MddExpressionRepresentation.of(canonizedExpr, decl, mddVariable, expressionMddBuilder, transExpr);

        // Create child based on valuation and cache

        return newRepresentation;
    }
}
