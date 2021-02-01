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

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.analysis.expr.ExprStateUtils.anyUncoveredSuccessor;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static java.util.Collections.singleton;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.solver.Solver;

public final class ExprTraceUtils {

	private ExprTraceUtils() {
	}

	public static <A extends ExprAction> Trace<ExprState, A> traceFrom(final List<? extends A> actions) {
		checkNotNull(actions);
		final List<ExprState> states = new ArrayList<>(actions.size() + 1);
		for (int i = 0; i < actions.size() + 1; i++) {
			states.add(BasicExprState.of(True()));
		}
		return Trace.of(states, actions);
	}

	public static boolean isInductive(final Trace<? extends ExprState, ? extends ExprAction> trace,
									  final Solver solver) {
		for (int i = 0; i < trace.length(); i++) {
			final ExprState sourceState = trace.getState(i);
			final ExprAction action = trace.getAction(i);
			final ExprState targetState = trace.getState(i + 1);

			final Optional<Valuation> uncoveredSuccessor = anyUncoveredSuccessor(sourceState, action,
					singleton(targetState), solver);
			if (uncoveredSuccessor.isPresent()) {
				return false;
			}
		}
		return true;
	}

}
