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
package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public final class CfaAnalysis<S extends ExprState, P extends Prec>
		implements Analysis<CfaState<S>, CfaAction, CfaPrec<P>> {

	private final Domain<CfaState<S>> domain;
	private final InitFunc<CfaState<S>, CfaPrec<P>> initFunc;
	private final TransferFunc<CfaState<S>, CfaAction, CfaPrec<P>> transferFunc;

	private CfaAnalysis(final Loc initLoc, final Analysis<S, ? super CfaAction, ? super P> analysis) {
		checkNotNull(initLoc);
		checkNotNull(analysis);
		domain = CfaDomain.create(analysis.getDomain());
		initFunc = CfaInitFunc.create(initLoc, analysis.getInitFunc());
		transferFunc = CfaTransferFunc.create(analysis.getTransferFunc());
	}

	public static <S extends ExprState, P extends Prec> CfaAnalysis<S, P> create(final Loc initLoc,
			final Analysis<S, ? super CfaAction, ? super P> analysis) {
		return new CfaAnalysis<>(initLoc, analysis);
	}

	@Override
	public Domain<CfaState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<CfaState<S>, CfaPrec<P>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<CfaState<S>, CfaAction, CfaPrec<P>> getTransferFunc() {
		return transferFunc;
	}

}
