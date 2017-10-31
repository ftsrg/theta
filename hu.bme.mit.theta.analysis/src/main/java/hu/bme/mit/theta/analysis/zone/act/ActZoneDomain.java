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

import hu.bme.mit.theta.analysis.Domain;

public final class ActZoneDomain implements Domain<ActZoneState> {

	private ActZoneDomain() {
	}

	private static class LazyHolder {
		static final ActZoneDomain INSTANCE = new ActZoneDomain();
	}

	public static ActZoneDomain getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public boolean isBottom(final ActZoneState state) {
		return state.isBottom();
	}

	@Override
	public boolean isLeq(final ActZoneState state1, final ActZoneState state2) {
		return state1.isLeq(state2);
	}

}
