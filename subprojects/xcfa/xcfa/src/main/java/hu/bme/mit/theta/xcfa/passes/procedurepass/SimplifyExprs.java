/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.passes.procedurepass;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.utils.ExprSimplifier;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.ProcedureCall;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class SimplifyExprs extends ProcedurePass {

    @Override
    public XcfaProcedure.Builder run(XcfaProcedure.Builder builder) {
        for (XcfaEdge edge : new ArrayList<>(builder.getEdges())) {
            XcfaEdge newEdge = edge.mapLabels(label -> {
                if (label instanceof XcfaLabel.StmtXcfaLabel
                    && label.getStmt() instanceof AssignStmt
                    && !(((AssignStmt<?>) label.getStmt()).getVarDecl()
                    .getType() instanceof ArrayType)) {
                    VarDecl<?> varDecl = ((AssignStmt<?>) label.getStmt()).getVarDecl();
                    Expr<?> expr = ((AssignStmt<?>) label.getStmt()).getExpr();
                    Expr<?> simplified = ExprSimplifier.simplify(expr, ImmutableValuation.empty());
                    if (FrontendMetadata.getMetadataValue(expr, "cType").isPresent()) {
                        FrontendMetadata.create(simplified, "cType", CComplexType.getType(expr));
                    }
                    if (FrontendMetadata.getMetadataValue(varDecl.getRef(), "cType").isPresent()) {
                        simplified = ExprSimplifier.simplify(
                            CComplexType.getType(varDecl.getRef()).castTo(simplified),
                            ImmutableValuation.empty());
                        FrontendMetadata.create(simplified, "cType",
                            CComplexType.getType(varDecl.getRef()));
                    }
                    Stmt newStmt = Assign(
                        cast(varDecl, varDecl.getType()),
                        cast(simplified, varDecl.getType()));
                    return Stmt(newStmt);
                } else if (label instanceof XcfaLabel.ProcedureCallXcfaLabel) {
                    List<Expr<?>> newExprs = ((XcfaLabel.ProcedureCallXcfaLabel) label).getParams()
                        .stream().map((Expr<?> expr) -> {
                            final Expr<?> simplified = ExprUtils.simplify(expr);
                            if (FrontendMetadata.getMetadataValue(expr, "cType").isPresent()) {
                                FrontendMetadata.create(simplified, "cType",
                                    CComplexType.getType(expr));
                            }
                            return simplified;
                        }).collect(Collectors.toList());
                    return ProcedureCall(newExprs,
                        ((XcfaLabel.ProcedureCallXcfaLabel) label).getProcedure());
                } else {
                    return label;
                }
            });
            if (!edge.getLabels().equals(newEdge.getLabels())) {
                builder.removeEdge(edge);
                builder.addEdge(newEdge);
            }
        }
        return builder;
    }

    @Override
    public boolean isPostInlining() {
        return true;
    }
}