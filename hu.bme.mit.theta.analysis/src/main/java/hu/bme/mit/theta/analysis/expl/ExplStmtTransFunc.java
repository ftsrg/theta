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

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplStmtSuccEvaluator.EvalResult;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.StmtUnfoldResult;
import hu.bme.mit.theta.core.utils.StmtUtils;
import hu.bme.mit.theta.core.utils.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

public final class ExplStmtTransFunc implements TransFunc<ExplState, StmtAction, ExplPrec> {

	private final Solver solver;
	private final Optional<Integer> maxSuccToEnumerate;

	private ExplStmtTransFunc(final Solver solver, final Optional<Integer> maxSuccToEnumerate) {
		this.solver = checkNotNull(solver);
		this.maxSuccToEnumerate = maxSuccToEnumerate;
	}

	public static ExplStmtTransFunc create(final Solver solver, final int maxSuccToEnumerate) {
		return create(solver, Optional.of(maxSuccToEnumerate));
	}

	public static ExplStmtTransFunc create(final Solver solver, final Optional<Integer> maxSuccToEnumerate) {
		checkArgument(!maxSuccToEnumerate.isPresent() || maxSuccToEnumerate.get() >= 0,
				"Max. states from solver must be non-negative.");
		return new ExplStmtTransFunc(solver, maxSuccToEnumerate);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final StmtAction action, final ExplPrec prec) {
		return getSuccStates(state, action.getStmts(), prec);
	}

	Collection<ExplState> getSuccStates(final ExplState state, final List<Stmt> stmts, final ExplPrec prec) {
		boolean triedSolver = false;
		ExplState running = state;

		for (int i = 0; i < stmts.size(); i++) {
			final Stmt stmt = stmts.get(i);
			final EvalResult evalResult = ExplStmtSuccEvaluator.evalSucc(running, stmt);
			if (!evalResult.isPrecise() && !triedSolver
					&& (!maxSuccToEnumerate.isPresent() || maxSuccToEnumerate.get() > 0)) {
				triedSolver = true;
				final List<Stmt> remainingStmts = stmts.subList(i, stmts.size());
				final StmtUnfoldResult toExprResult = StmtUtils.toExpr(remainingStmts, VarIndexing.all(0));
				final Expr<BoolType> expr = And(running.toExpr(), And(toExprResult.getExprs()));
				final VarIndexing nextIdx = toExprResult.getIndexing();
				// We query (max + 1) states from the solver to see if there
				// would be more than max
				final int maxToQuery = maxSuccToEnumerate.isPresent() ? maxSuccToEnumerate.get() + 1 : 0;
				final Collection<ExplState> succStates = ExprStates.createStatesForExpr(solver, expr, 0,
						prec::createState, nextIdx, maxToQuery);
				if (!maxSuccToEnumerate.isPresent() || succStates.size() <= maxSuccToEnumerate.get()) {
					return succStates;
				}
			}
			running = evalResult.getState();
		}

		if (running.isBottom()) {
			return Collections.singleton(running);
		} else {
			final ExplState abstracted = prec.createState(running);
			return Collections.singleton(abstracted);
		}
	}

}
