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
package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ItpZoneTransFunc<A extends Action> implements TransFunc<ItpZoneState, A, ZonePrec> {

	private final TransFunc<ZoneState, ? super A, ZonePrec> transFunc;

	private ItpZoneTransFunc(final TransFunc<ZoneState, ? super A, ZonePrec> transFunc) {
		this.transFunc = checkNotNull(transFunc);
	}

	public static <A extends Action> ItpZoneTransFunc<A> create(
			final TransFunc<ZoneState, ? super A, ZonePrec> transFunc) {
		return new ItpZoneTransFunc<>(transFunc);
	}

	////

	@Override
	public Collection<? extends ItpZoneState> getSuccStates(final ItpZoneState state, final A action,
			final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getZone();
		final Collection<? extends ZoneState> subSuccStates = transFunc.getSuccStates(subState, action, prec);

		if (subSuccStates.isEmpty()) {
			final ItpZoneState succState = ItpZoneState.of(ZoneState.bottom(), ZoneState.top());
			return Collections.singleton(succState);
		} else {
			final Collection<ItpZoneState> result = new ArrayList<>(subSuccStates.size());
			for (final ZoneState subSuccState : subSuccStates) {
				final ItpZoneState succState = ItpZoneState.of(subSuccState, ZoneState.top());
				result.add(succState);
			}
			return result;
		}
	}
}
