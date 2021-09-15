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

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.utils.PathUtils.extractValuation;
import static hu.bme.mit.theta.core.utils.PathUtils.unfold;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.utils.WithPushPop;

public final class ExprStateUtils {

	private ExprStateUtils() {
	}

	public static Optional<Valuation> anyUncoveredSuccessor(final ExprState state, final ExprAction action,
															final Collection<? extends ExprState> succStates, final Solver solver) {
		try (WithPushPop wpp = new WithPushPop(solver)) {
			final VarIndexing indexing = action.nextIndexing();
			solver.add(unfold(state.toExpr(), 0));
			solver.add(unfold(action.toExpr(), 0));
			for (final ExprState succState : succStates) {
				solver.add(Not(unfold(succState.toExpr(), indexing)));
			}
			final SolverStatus status = solver.check();

			if (status.isUnsat()) {
				return Optional.empty();
			} else if (status.isSat()) {
				final Valuation model = solver.getModel();
				final Valuation valuation = extractValuation(model, indexing);
				return Optional.of(valuation);
			} else {
				throw new AssertionError();
			}
		}
	}

	public static Optional<Valuation> anyUncoveredPredecessor(final Collection<? extends ExprState> predStates,
															  final ExprAction action, final ExprState state, final Solver solver) {
		try (WithPushPop wpp = new WithPushPop(solver)) {
			final VarIndexing indexing = action.nextIndexing();
			for (final ExprState predState : predStates) {
				solver.add(Not(unfold(predState.toExpr(), 0)));
			}
			solver.add(unfold(action.toExpr(), 0));
			solver.add(unfold(state.toExpr(), indexing));
			final SolverStatus status = solver.check();

			if (status.isUnsat()) {
				return Optional.empty();
			} else if (status.isSat()) {
				final Valuation model = solver.getModel();
				final Valuation valuation = extractValuation(model, 0);
				return Optional.of(valuation);
			} else {
				throw new AssertionError();
			}
		}
	}
}
