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

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;

public final class PredAnalysis<A extends ExprAction> implements Analysis<PredState, A, PredPrec> {

	private final PartialOrd<PredState> partialOrd;
	private final InitFunc<PredState, PredPrec> initFunc;
	private final TransFunc<PredState, A, PredPrec> transFunc;

	private PredAnalysis(final Solver solver, final PredAbstractor predAbstractor, final Expr<BoolType> initExpr) {
		partialOrd = PredOrd.create(solver);
		initFunc = PredInitFunc.create(predAbstractor, initExpr);
		transFunc = PredTransFunc.create(predAbstractor);
	}

	public static <A extends ExprAction> PredAnalysis<A> create(final Solver solver, final PredAbstractor predAbstractor,
									  final Expr<BoolType> initExpr) {
		return new PredAnalysis<A>(solver, predAbstractor, initExpr);
	}

	////

	@Override
	public PartialOrd<PredState> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<PredState, PredPrec> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<PredState, A, PredPrec> getTransFunc() {
		return transFunc;
	}

}
