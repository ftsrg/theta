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
package hu.bme.mit.theta.formalism.xta.analysis.zone;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.TransferFunc;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;

final class XtaZoneTransferFunc implements TransferFunc<ZoneState, XtaAction, ZonePrec> {

	private final static XtaZoneTransferFunc INSTANCE = new XtaZoneTransferFunc();

	private XtaZoneTransferFunc() {
	}

	static XtaZoneTransferFunc getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<ZoneState> getSuccStates(final ZoneState state, final XtaAction action, final ZonePrec prec) {

		final ZoneState succState = XtaZoneUtils.post(state, action, prec);

		if (succState.isBottom()) {
			return ImmutableList.of();
		} else {
			return ImmutableList.of(succState);
		}
	}

}
