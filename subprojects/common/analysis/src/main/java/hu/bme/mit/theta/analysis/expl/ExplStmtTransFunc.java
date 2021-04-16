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
package hu.bme.mit.theta.analysis.expl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static java.util.Collections.singleton;

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.StmtApplier.ApplyResult;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.model.MutableValuation;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

public final class ExplStmtTransFunc implements TransFunc<ExplState, StmtAction, ExplPrec> {

	private final Solver solver;
	// 0 means arbitrarily many
	private final int maxSuccToEnumerate;

	private ExplStmtTransFunc(final Solver solver, final int maxSuccToEnumerate) {
		this.solver = checkNotNull(solver);
		this.maxSuccToEnumerate = maxSuccToEnumerate;
	}

	public static ExplStmtTransFunc create(final Solver solver, final int maxSuccToEnumerate) {
		checkArgument(maxSuccToEnumerate >= 0, "Max. succ. to enumerate must be non-negative.");
		return new ExplStmtTransFunc(solver, maxSuccToEnumerate);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final StmtAction action, final ExplPrec prec) {
		return getSuccStates(state, action.getStmts(), prec);
	}

	Collection<ExplState> getSuccStates(final ExplState state, final List<Stmt> stmts, final ExplPrec prec) {
		final MutableValuation val = MutableValuation.copyOf(state);
		boolean triedSolver = false;

		for (int i = 0; i < stmts.size(); i++) {
			final Stmt stmt = stmts.get(i);
			final ApplyResult applyResult = StmtApplier.apply(stmt, val, triedSolver);

			assert !triedSolver || applyResult != ApplyResult.BOTTOM;

			if (applyResult == ApplyResult.BOTTOM) {
				return singleton(ExplState.bottom());
			} else if (applyResult == ApplyResult.FAILURE) {
				triedSolver = true;
				final List<Stmt> remainingStmts = stmts.subList(i, stmts.size());
				final StmtUnfoldResult toExprResult = StmtUtils.toExpr(remainingStmts, VarIndexing.all(0));
				final Expr<BoolType> expr = And(val.toExpr(), And(toExprResult.getExprs()));
				final VarIndexing nextIdx = toExprResult.getIndexing();
				// We query (max + 1) states from the solver to see if there
				// would be more than max
				final int maxToQuery = maxSuccToEnumerate == 0 ? 0 : maxSuccToEnumerate + 1;
				final Collection<ExplState> succStates = ExprStates.createStatesForExpr(solver, expr, 0,
						prec::createState, nextIdx, maxToQuery);

				if (succStates.isEmpty()) {
					return singleton(ExplState.bottom());
				} else if (maxSuccToEnumerate == 0 || succStates.size() <= maxSuccToEnumerate) {
					return succStates;
				} else {
					final ApplyResult reapplyResult = StmtApplier.apply(stmt, val, true);
					assert reapplyResult == ApplyResult.SUCCESS;
				}
			}
		}

		final ExplState abstracted = prec.createState(val);
		return singleton(abstracted);
	}

}
