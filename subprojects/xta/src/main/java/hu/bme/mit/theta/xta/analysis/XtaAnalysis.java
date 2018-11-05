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
package hu.bme.mit.theta.xta.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.xta.XtaSystem;

public final class XtaAnalysis<S extends State, P extends Prec> implements Analysis<XtaState<S>, XtaAction, P> {
	private final PartialOrd<XtaState<S>> partialOrd;
	private final InitFunc<XtaState<S>, P> initFunc;
	private final TransFunc<XtaState<S>, XtaAction, P> transFunc;

	private XtaAnalysis(final XtaSystem system, final Analysis<S, ? super XtaAction, ? super P> analysis) {
		checkNotNull(system);
		checkNotNull(analysis);
		partialOrd = XtaOrd.create(analysis.getPartialOrd());
		initFunc = XtaInitFunc.create(system, analysis.getInitFunc());
		transFunc = XtaTransFunc.create(analysis.getTransFunc());
	}

	public static <S extends State, P extends Prec> XtaAnalysis<S, P> create(final XtaSystem system,
			final Analysis<S, ? super XtaAction, ? super P> analysis) {
		return new XtaAnalysis<>(system, analysis);
	}

	@Override
	public PartialOrd<XtaState<S>> getPartialOrd() {
		return partialOrd;
	}

	@Override
	public InitFunc<XtaState<S>, P> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XtaState<S>, XtaAction, P> getTransFunc() {
		return transFunc;
	}

}
