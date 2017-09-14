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
package hu.bme.mit.theta.analysis.zone.act;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ActZoneInitFunc implements InitFunc<ActZoneState, ZonePrec> {

	private final InitFunc<ZoneState, ZonePrec> initFunc;

	private ActZoneInitFunc(final InitFunc<ZoneState, ZonePrec> initFunc) {
		this.initFunc = checkNotNull(initFunc);
	}

	public static ActZoneInitFunc create(final InitFunc<ZoneState, ZonePrec> initFunc) {
		return new ActZoneInitFunc(initFunc);
	}

	////

	@Override
	public Collection<? extends ActZoneState> getInitStates(final ZonePrec prec) {
		checkNotNull(prec);
		final Collection<ActZoneState> result = new ArrayList<>();
		final Collection<? extends ZoneState> subInitStates = initFunc.getInitStates(prec);
		for (final ZoneState subInitState : subInitStates) {
			final ActZoneState initState = ActZoneState.of(subInitState, ImmutableSet.of());
			result.add(initState);
		}
		return result;
	}

}
