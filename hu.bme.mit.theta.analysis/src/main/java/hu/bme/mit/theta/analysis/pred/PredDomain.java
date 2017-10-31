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
package hu.bme.mit.theta.analysis.pred;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

public final class PredDomain implements Domain<PredState> {

	private final Solver solver;

	public static PredDomain create(final Solver solver) {
		return new PredDomain(solver);
	}

	private PredDomain(final Solver solver) {
		this.solver = checkNotNull(solver);
	}

	@Override
	public boolean isBottom(final PredState state) {
		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(PathUtils.unfold(state.toExpr(), 0));
			return solver.check().isUnsat();
		}
	}

	@Override
	public boolean isLeq(final PredState state1, final PredState state2) {
		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(PathUtils.unfold(state1.toExpr(), 0));
			solver.add(PathUtils.unfold(Not(state2.toExpr()), 0));
			return solver.check().isUnsat();
		}
	}

}
