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
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.utils.PathUtils.unfold;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

public final class ExprDomain implements Domain<ExprState> {

	private final Solver solver;

	private ExprDomain(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	public static ExprDomain create(final Solver solver) {
		return new ExprDomain(solver);
	}

	@Override
	public boolean isLeq(final ExprState state1, final ExprState state2) {
		checkNotNull(state1);
		checkNotNull(state2);

		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(unfold(state1.toExpr(), 0));
			solver.add(Not(unfold(state2.toExpr(), 0)));
			return solver.check().isUnsat();
		}
	}

}
