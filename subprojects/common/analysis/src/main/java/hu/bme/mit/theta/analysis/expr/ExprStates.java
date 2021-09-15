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

import java.util.ArrayList;
import java.util.Collection;
import java.util.function.Function;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

/**
 * Utility for generating ExprStates.
 */
public final class ExprStates {

	private ExprStates() {
	}

	/**
	 * Generate all states that satisfy a given expression.
	 *
	 * @param solver           Solver
	 * @param expr             Expression to be satisfied
	 * @param exprIndex        Index for unfolding the expression
	 * @param valuationToState Mapping from a valuation to a state
	 * @param stateIndexing    Index for extracting the state
	 * @return States satisfying the expression
	 */
	public static <S extends ExprState> Collection<S> createStatesForExpr(final Solver solver,
																		  final Expr<BoolType> expr, final int exprIndex,
																		  final Function<? super Valuation, ? extends S> valuationToState, final VarIndexing stateIndexing) {
		return createStatesForExpr(solver, expr, exprIndex, valuationToState, stateIndexing, 0);
	}

	/**
	 * Generate all or a limited number of states that satisfy a given
	 * expression.
	 *
	 * @param solver           Solver
	 * @param expr             Expression to be satisfied
	 * @param exprIndex        Index for unfolding the expression
	 * @param valuationToState Mapping from a valuation to a state
	 * @param stateIndexing    Index for extracting the state
	 * @param limit            Limit the number of states to generate (0 is unlimited)
	 * @return States satisfying the expression
	 */
	public static <S extends ExprState> Collection<S> createStatesForExpr(final Solver solver,
																		  final Expr<BoolType> expr, final int exprIndex,
																		  final Function<? super Valuation, ? extends S> valuationToState, final VarIndexing stateIndexing,
																		  final int limit) {
		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(PathUtils.unfold(expr, exprIndex));

			final Collection<S> result = new ArrayList<>();
			while (solver.check().isSat() && (limit == 0 || result.size() < limit)) {
				final Valuation model = solver.getModel();
				final Valuation valuation = PathUtils.extractValuation(model, stateIndexing);
				final S state = valuationToState.apply(valuation);
				result.add(state);
				solver.add(Not(PathUtils.unfold(state.toExpr(), stateIndexing)));
			}
			return result;
		}
	}
}
