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
package hu.bme.mit.theta.formalism.xta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ItpZoneInitFunc implements InitFunc<ItpZoneState, ZonePrec> {

	private final InitFunc<ZoneState, ZonePrec> initFunc;

	private ItpZoneInitFunc(final InitFunc<ZoneState, ZonePrec> initFunc) {
		this.initFunc = checkNotNull(initFunc);
	}

	public static ItpZoneInitFunc create(final InitFunc<ZoneState, ZonePrec> initFunc) {
		return new ItpZoneInitFunc(initFunc);
	}

	////

	@Override
	public Collection<ItpZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<ItpZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunc.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final ItpZoneState initState = ItpZoneState.of(subInitState, ZoneState.top());
			result.add(initState);
		}
		return result;
	}

}
