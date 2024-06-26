/*
 *  Copyright 2024 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.cfa.analysis;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.AbstractMonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Neq;

public class CfaToMonoliticTransFunc extends AbstractMonolithicTransFunc {
    private CfaToMonoliticTransFunc(CFA cfa) {
        Preconditions.checkArgument(cfa.getErrorLoc().isPresent());

        int i = 0;
        final Map<CFA.Loc, Integer> map = new HashMap<>();
        for (var x : cfa.getLocs()) {
            map.put(x, i++);
        }
        var locVar = Decls.Var("loc", Int());
        List<Stmt> tranList = cfa.getEdges().stream().map(e -> SequenceStmt.of(List.of(
                AssumeStmt.of(Eq(locVar.getRef(), Int(map.get(e.getSource())))),
                e.getStmt(),
                AssignStmt.of(locVar, Int(map.get(e.getTarget())))
        ))).collect(Collectors.toList());
        var trans = NonDetStmt.of(tranList);
        var transUnfold = StmtUtils.toExpr(trans, VarIndexingFactory.indexing(0));
        transExpr = And(transUnfold.getExprs());
        initExpr = Eq(locVar.getRef(), Int(map.get(cfa.getInitLoc())));
        propExpr = Neq(locVar.getRef(), Int(map.get(cfa.getErrorLoc().get())));

        firstIndex = VarIndexingFactory.indexing(0);
        offsetIndex = transUnfold.getIndexing();
    }

    public static MonolithicTransFunc create(CFA cfa) {
        return new CfaToMonoliticTransFunc(cfa);
    }
}
