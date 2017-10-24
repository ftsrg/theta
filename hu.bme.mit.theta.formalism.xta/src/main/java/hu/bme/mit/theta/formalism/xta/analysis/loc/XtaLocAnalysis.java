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
package hu.bme.mit.theta.formalism.xta.analysis.loc;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;

public final class XtaLocAnalysis<S extends State, P extends Prec> implements Analysis<XtaLocState<S>, XtaAction, P> {

	private final Domain<XtaLocState<S>> domain;
	private final InitFunc<XtaLocState<S>, P> initFunc;
	private final TransFunc<XtaLocState<S>, XtaAction, P> transFunc;

	private XtaLocAnalysis(final XtaSystem system, final Analysis<S, ? super XtaAction, ? super P> analysis) {
		checkNotNull(system);
		checkNotNull(analysis);
		domain = XtaLocDomain.create(analysis.getDomain());
		initFunc = XtaLocInitFunc.create(system, analysis.getInitFunc());
		transFunc = XtaLocTransFunc.create(analysis.getTransFunc());
	}

	public static <S extends State, P extends Prec> XtaLocAnalysis<S, P> create(final XtaSystem system,
			final Analysis<S, ? super XtaAction, ? super P> analysis) {
		return new XtaLocAnalysis<>(system, analysis);
	}

	@Override
	public Domain<XtaLocState<S>> getDomain() {
		return domain;
	}

	@Override
	public InitFunc<XtaLocState<S>, P> getInitFunc() {
		return initFunc;
	}

	@Override
	public TransFunc<XtaLocState<S>, XtaAction, P> getTransFunc() {
		return transFunc;
	}

}
