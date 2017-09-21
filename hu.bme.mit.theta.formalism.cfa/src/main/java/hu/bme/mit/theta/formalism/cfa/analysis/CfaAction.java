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
package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.utils.VarIndexing.all;

import java.util.Collections;
import java.util.List;

import hu.bme.mit.theta.analysis.expl.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.formalism.cfa.CFA.Edge;

public final class CfaAction implements StmtAction {

	private final Edge edge;
	private final Expr<BoolType> expr;
	private final VarIndexing nextIndexing;

	private CfaAction(final Edge edge) {
		this.edge = checkNotNull(edge);

		// TODO: do the following stuff lazily
		final StmtUnfoldResult toExprResult = StmtUtils.toExpr(edge.getStmt(), all(0));
		expr = And(toExprResult.getExprs());
		nextIndexing = toExprResult.getIndexing();
	}

	public static CfaAction create(final Edge edge) {
		return new CfaAction(edge);
	}

	public Edge getEdge() {
		return edge;
	}

	@Override
	public Expr<BoolType> toExpr() {
		return expr;
	}

	@Override
	public VarIndexing nextIndexing() {
		return nextIndexing;
	}

	@Override
	public List<Stmt> getStmts() {
		return Collections.singletonList(edge.getStmt());
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).add(edge.getStmt()).toString();
	}
}
