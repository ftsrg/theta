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

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class ExplAnalysis implements Analysis<ExplState, ExprAction, ExplPrec> {

	private final Domain<ExplState> domain;
	private final InitFunc<ExplState, ExplPrec> initFunc;
	private final TransFunc<ExplState, ExprAction, ExplPrec> transFunc;

	private ExplAnalysis(final Solver solver, final Expr<BoolType> initExpr) {
		checkNotNull(solver);
		checkNotNull(initExpr);
		this.domain = ExplDomain.getInstance();
		this.initFunc = ExplInitFunc.create(solver, initExpr);
		this.transFunc = ExplTransFunc.create(solver);

	}

	public static ExplAnalysis create(final Solver solver, final Expr<BoolType> initExpr) {
		return new ExplAnalysis(solver, initExpr);
	}

	@Override
	public Domain<ExplState> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<ExplState, ExplPrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<ExplState, ExprAction, ExplPrec> getTransFunc() {
		return transFunc;
	}

}
