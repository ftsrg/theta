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

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.pred.PredAbstractors.PredAbstractor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;

import java.util.Collection;
import java.util.Collections;

import static com.google.common.base.Preconditions.checkNotNull;

public final class PredInitFunc implements InitFunc<PredState, PredPrec> {

	private final Expr<BoolType> initExpr;
	private final PredAbstractor predAbstractor;

	private PredInitFunc(final PredAbstractor predAbstractor, final Expr<BoolType> initExpr) {
		this.initExpr = checkNotNull(initExpr);
		this.predAbstractor = checkNotNull(predAbstractor);
	}

	public static PredInitFunc create(final PredAbstractor predAbstractor, final Expr<BoolType> expr) {
		return new PredInitFunc(predAbstractor, expr);
	}

	@Override
	public Collection<? extends PredState> getInitStates(final PredPrec prec) {
		checkNotNull(prec);
		final Collection<PredState> initStates = predAbstractor.createStatesForExpr(initExpr, VarIndexingFactory.indexing(0), prec,
				VarIndexingFactory.indexing(0));
		return initStates.isEmpty() ? Collections.singleton(PredState.bottom()) : initStates;
	}

}
