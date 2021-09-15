/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.expr;

import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;

import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And;
import static hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory.indexing;

public abstract class StmtAction implements ExprAction {

	private volatile Expr<BoolType> expr = null;
	private volatile VarIndexing nextIndexing = null;

	public abstract List<Stmt> getStmts();

	@Override
	public final Expr<BoolType> toExpr() {
		Expr<BoolType> result = expr;
		if (result == null) {
			final StmtUnfoldResult toExprResult = StmtUtils.toExpr(getStmts(), indexing(0));
			expr = And(toExprResult.getExprs());
			nextIndexing = toExprResult.getIndexing();
			result = expr;
		}
		return result;
	}

	@Override
	public final VarIndexing nextIndexing() {
		VarIndexing result = nextIndexing;
		if (result == null) {
			final StmtUnfoldResult toExprResult = StmtUtils.toExpr(getStmts(), indexing(0));
			expr = And(toExprResult.getExprs());
			nextIndexing = toExprResult.getIndexing();
			result = nextIndexing;
		}
		return result;
	}

}
