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
package hu.bme.mit.theta.formalism.xta.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaAnalysis<S extends State, P extends Prec> implements Analysis<XtaState<S>, XtaAction, P> {
	private final Domain<XtaState<S>> domain;
	private final InitFunc<XtaState<S>, P> initFunc;
	private final TransferFunc<XtaState<S>, XtaAction, P> transferFunc;

	private XtaAnalysis(final XtaSystem system, final Analysis<S, ? super XtaAction, ? super P> analysis) {
		checkNotNull(system);
		checkNotNull(analysis);
		domain = XtaDomain.create(analysis.getDomain());
		initFunc = XtaInitFunc.create(system, analysis.getInitFunc());
		transferFunc = XtaTransferFunc.create(analysis.getTransferFunc());
	}

	public static <S extends State, P extends Prec> XtaAnalysis<S, P> create(final XtaSystem system,
			final Analysis<S, ? super XtaAction, ? super P> analysis) {
		return new XtaAnalysis<>(system, analysis);
	}

	@Override
	public Domain<XtaState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<XtaState<S>, P> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransferFunc<XtaState<S>, XtaAction, P> getTransferFunc() {
		return transferFunc;
	}

}
