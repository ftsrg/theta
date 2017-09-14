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

import java.util.function.Predicate;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.utils.WithPushPop;

public class ExprStatePredicate implements Predicate<ExprState> {

	private final Expr<BoolType> expr;
	private Expr<BoolType> expr0;
	private final Solver solver;

	public ExprStatePredicate(final Expr<BoolType> expr, final Solver solver) {
		this.expr = checkNotNull(expr);
		this.solver = checkNotNull(solver);
		this.expr0 = null;
	}

	@Override
	public boolean test(final ExprState state) {
		if (expr0 == null) {
			expr0 = PathUtils.unfold(expr, 0);
		}
		try (WithPushPop wpp = new WithPushPop(solver)) {
			solver.add(PathUtils.unfold(state.toExpr(), 0));
			solver.add(expr0);
			return solver.check().isSat();
		}
	}

	public Expr<BoolType> toExpr() {
		return expr;
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).add(expr).toString();
	}
}
