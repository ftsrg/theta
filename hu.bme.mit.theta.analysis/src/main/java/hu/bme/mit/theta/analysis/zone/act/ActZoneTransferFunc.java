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
import java.util.Collections;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class ActZoneTransferFunc<A extends Action> implements TransferFunc<ActZoneState, A, ZonePrec> {

	private final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc;

	private ActZoneTransferFunc(final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc) {
		this.transferFunc = checkNotNull(transferFunc);
	}

	public static <A extends Action> ActZoneTransferFunc<A> create(
			final TransferFunc<ZoneState, ? super A, ZonePrec> transferFunc) {
		return new ActZoneTransferFunc<>(transferFunc);
	}

	@Override
	public Collection<ActZoneState> getSuccStates(final ActZoneState state, final A action, final ZonePrec prec) {
		checkNotNull(state);
		checkNotNull(action);
		checkNotNull(prec);

		final ZoneState subState = state.getZone();
		final Collection<? extends ZoneState> subSuccStates = transferFunc.getSuccStates(subState, action, prec);

		if (subSuccStates.isEmpty()) {
			final ActZoneState succState = ActZoneState.of(ZoneState.bottom(), ImmutableSet.of());
			return Collections.singleton(succState);
		} else {
			final Collection<ActZoneState> result = new ArrayList<>(subSuccStates.size());
			for (final ZoneState subSuccState : subSuccStates) {
				final ActZoneState succState = ActZoneState.of(subSuccState, ImmutableSet.of());
				result.add(succState);
			}
			return result;
		}
	}

}
