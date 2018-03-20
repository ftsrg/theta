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

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Collections.singleton;

import java.util.Collection;

import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.XtaAction;

final class XtaExplTransFunc implements TransFunc<ExplState, XtaAction, UnitPrec> {

	private XtaExplTransFunc(final XtaSystem system) {
		// TODO remove parameter 'system'
		checkNotNull(system);
	}

	public static XtaExplTransFunc create(final XtaSystem system) {
		return new XtaExplTransFunc(system);
	}

	@Override
	public Collection<ExplState> getSuccStates(final ExplState state, final XtaAction action, final UnitPrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);
		return singleton(XtaExplUtils.post(state, action));
	}

}
