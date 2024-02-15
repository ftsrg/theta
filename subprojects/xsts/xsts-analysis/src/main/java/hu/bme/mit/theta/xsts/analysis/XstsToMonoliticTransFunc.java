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
package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.algorithm.AbstractMonolithicTransFunc;
import hu.bme.mit.theta.analysis.algorithm.MonolithicTransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;

public class XstsToMonoliticTransFunc extends AbstractMonolithicTransFunc {
    private XstsToMonoliticTransFunc(XSTS xsts) {
        final StmtUnfoldResult initUnfoldResult = StmtUtils.toExpr(xsts.getInit(), VarIndexingFactory.indexing(0));
        initExpr = And(And(initUnfoldResult.getExprs()), xsts.getInitFormula());
        firstIndex = initUnfoldResult.getIndexing();
        final var envTran = Stmts.SequenceStmt(List.of(xsts.getEnv(), xsts.getTran()));
        final StmtUnfoldResult envTranUnfoldResult = StmtUtils.toExpr(envTran, VarIndexingFactory.indexing(0));
        transExpr = And(envTranUnfoldResult.getExprs());
        offsetIndex = envTranUnfoldResult.getIndexing();
        propExpr = xsts.getProp();

    }

    public static MonolithicTransFunc create(XSTS xsts) {
        return new XstsToMonoliticTransFunc(xsts);
    }
}
