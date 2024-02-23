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

package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

public final class MonolithicTransFuncStub implements MonolithicTransFunc {
    private final Expr<BoolType> transExpr;
    private final Expr<BoolType> initExpr;
    private final Expr<BoolType> propExpr;
    private final VarIndexing initIndexing;
    private final VarIndexing offsetIndexing;

    public MonolithicTransFuncStub(
            Stmt transStmt,
            Expr<BoolType> initExpr,
            Expr<BoolType> propExpr
    ) {
        var result = StmtUtils.toExpr(transStmt, VarIndexingFactory.indexing(0));
        this.transExpr = And(result.getExprs());
        this.initExpr = initExpr;
        this.propExpr = propExpr;
        this.initIndexing = VarIndexingFactory.indexing(0);
        this.offsetIndexing = result.getIndexing();
    }

    @Override
    public Expr<BoolType> getTransExpr() {
        return transExpr;
    }

    @Override
    public Expr<BoolType> getInitExpr() {
        return initExpr;
    }

    @Override
    public Expr<BoolType> getPropExpr() {
        return propExpr;
    }

    @Override
    public VarIndexing getInitIndexing() {
        return initIndexing;
    }

    @Override
    public VarIndexing getOffsetIndexing() {
        return offsetIndexing;
    }

}
