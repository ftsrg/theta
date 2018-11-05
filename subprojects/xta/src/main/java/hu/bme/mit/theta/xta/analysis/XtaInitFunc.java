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

import java.util.Collection;
import java.util.List;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.XtaProcess.Loc;

final class XtaInitFunc<S extends State, P extends Prec> implements InitFunc<XtaState<S>, P> {
	private final XtaSystem system;
	private final InitFunc<S, ? super P> initFunc;

	private XtaInitFunc(final XtaSystem system, final InitFunc<S, ? super P> initFunc) {
		this.system = checkNotNull(system);
		this.initFunc = checkNotNull(initFunc);
	}

	public static <S extends State, P extends Prec> XtaInitFunc<S, P> create(final XtaSystem system,
			final InitFunc<S, ? super P> initFunc) {
		return new XtaInitFunc<>(system, initFunc);
	}

	@Override
	public Collection<XtaState<S>> getInitStates(final P prec) {
		checkNotNull(prec);
		final List<Loc> initLocs = system.getInitLocs();
		final Collection<? extends S> initStates = initFunc.getInitStates(prec);
		return XtaState.collectionOf(initLocs, initStates);
	}

}
