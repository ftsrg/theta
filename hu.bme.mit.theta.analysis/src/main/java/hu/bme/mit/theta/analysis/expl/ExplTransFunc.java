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

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.solver.Solver;

public final class ExplTransFunc implements TransFunc<ExplState, ExprAction, ExplPrec> {

	private final Solver solver;

	private ExplTransFunc(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static ExplTransFunc create(final Solver solver) {
		return new ExplTransFunc(solver);
	}

	@Override
	public Collection<? extends ExplState> getSuccStates(final ExplState state, final ExprAction action,
			final ExplPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		final Collection<ExplState> succStates = ExprStates.createStatesForExpr(solver,
				BoolExprs.And(state.toExpr(), action.toExpr()), 0, prec::createState, action.nextIndexing());
		return succStates.isEmpty() ? Collections.singleton(ExplState.bottom()) : succStates;
	}

}
