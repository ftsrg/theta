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

package hu.bme.mit.theta.xcfa.analysis.por;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xcfa.UtilsKt;
import hu.bme.mit.theta.xcfa.model.StmtLabel;
import hu.bme.mit.theta.xcfa.model.XCFA;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;

public class XcfaToKindImc {
    Expr<BoolType> transExpr;
    Expr<BoolType> initExpr;
    Expr<BoolType> propExpr;
    int upperBound;
    SolverFactory solverFactory1;
    Set<VarDecl<?>> vars;
    StmtUnfoldResult transUnfold;


    public XcfaToKindImc(XCFA xcfa, int bound, SolverFactory solverFactory) {
        Preconditions.checkArgument(xcfa.getInitProcedures().size() == 1);

        var proc = xcfa.getInitProcedures().stream().findFirst().orElse(null).getFirst();
        assert proc != null;
        Preconditions.checkArgument(proc.getEdges().stream().map(UtilsKt::getFlatLabels).noneMatch(it -> it.stream().anyMatch(i -> !(i instanceof StmtLabel))));
        Preconditions.checkArgument(proc.getErrorLoc().isPresent());
        int i = 0;
        final Map<XcfaLocation, Integer> map = new HashMap<>();
        for (var x : proc.getLocs()) {
            map.put(x, i++);
        }
        var locVar = Decls.Var("loc", Int());
        List<Stmt> tranList = proc.getEdges().stream().map(e -> SequenceStmt.of(List.of(
                AssumeStmt.of(Eq(locVar.getRef(), Int(map.get(e.getSource())))),
                e.getLabel().toStmt(),
                AssignStmt.of(locVar, Int(map.get(e.getTarget())))
        ))).collect(Collectors.toList());
        final var trans = NonDetStmt.of(tranList);
        transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
        transExpr = And(transUnfold.getExprs());
        vars = ExprUtils.getVars(transExpr);
        initExpr = Eq(locVar.getRef(), Int(map.get(proc.getInitLoc())));
        propExpr = Neq(locVar.getRef(), Int(map.get(proc.getErrorLoc().get())));
        upperBound = bound;
        solverFactory1 = solverFactory;

    }
}
