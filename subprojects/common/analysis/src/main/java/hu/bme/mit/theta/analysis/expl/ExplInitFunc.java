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

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expr.ExprStates;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import hu.bme.mit.theta.solver.Solver;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;

public final class ExplInitFunc implements InitFunc<ExplState, ExplPrec> {

	private final Solver solver;
	private final Expr<BoolType> initExpr;

	private ExplInitFunc(final Solver solver, final Expr<BoolType> initExpr) {
		this.solver = checkNotNull(solver);
		this.initExpr = checkNotNull(initExpr);
	}

	public static ExplInitFunc create(final Solver solver, final Expr<BoolType> initExpr) {
		return new ExplInitFunc(solver, initExpr);
	}

	@Override
	public Collection<? extends ExplState> getInitStates(final ExplPrec prec) {
		checkNotNull(prec);
		final Collection<ExplState> initStates = ExprStates.createStatesForExpr(solver, initExpr, 0, prec::createState,
				VarIndexingFactory.indexing(0));
		return initStates.isEmpty() ? Collections.singleton(ExplState.bottom()) : initStates;
	}

}
