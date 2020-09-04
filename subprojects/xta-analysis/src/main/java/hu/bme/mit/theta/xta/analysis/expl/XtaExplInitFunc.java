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
package hu.bme.mit.theta.xta.analysis.expl;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.xta.XtaSystem;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

final class XtaExplInitFunc implements InitFunc<ExplState, UnitPrec> {

	private final XtaSystem system;

	private XtaExplInitFunc(final XtaSystem system) {
		this.system = checkNotNull(system);
	}

	public static XtaExplInitFunc create(final XtaSystem system) {
		return new XtaExplInitFunc(system);
	}

	@Override
	public Collection<ExplState> getInitStates(final UnitPrec prec) {
		checkNotNull(prec);
		final ExplState initState = ExplState.of(system.getInitVal());
		return singleton(initState);
	}

}
