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
package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.MultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.StackableExprState;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaAnalysis<S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, P extends Prec>
		implements Analysis<XcfaState<S, SS, SSS>, XcfaAction, XcfaPrec<P>> {

	private final PartialOrd<XcfaState<S, SS, SSS>> partialOrd;
	private final InitFunc<XcfaState<S, SS, SSS>, XcfaPrec<P>> initFunc;
	private final XcfaTransFunc<S, SS, SSS, P> transFunc;

	private XcfaAnalysis(final Map<Integer, XcfaLocation> initLocs, final Analysis<S, ? super XcfaAction, ? super P> analysis) {
		checkNotNull(initLocs);
		checkNotNull(analysis);
		partialOrd = XcfaOrd.create(analysis.getPartialOrd());
		initFunc = XcfaInitFunc.create(initLocs, analysis.getInitFunc());
		transFunc = XcfaTransFunc.create(analysis.getTransFunc());
	}

	public static <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>, P extends Prec> XcfaAnalysis<S, SS, SSS, P> create(final Map<Integer, XcfaLocation> initLocs,
																				  final Analysis<S, ? super XcfaAction, ? super P> analysis) {
		return new XcfaAnalysis<>(initLocs, analysis);
	}

	@Override
	public PartialOrd<XcfaState<S, SS, SSS>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<XcfaState<S, SS, SSS>, XcfaPrec<P>> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XcfaState<S, SS, SSS>, XcfaAction, XcfaPrec<P>> getTransFunc() {
		return transFunc;
	}

}
