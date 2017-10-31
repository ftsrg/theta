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

import hu.bme.mit.theta.analysis.Domain;

public final class ItpZoneDomain implements Domain<ItpZoneState> {

	private static final ItpZoneDomain INSTANCE = new ItpZoneDomain();

	private ItpZoneDomain() {
	}

	public static ItpZoneDomain getInstance() {
		return INSTANCE;
	}

	////

	@Override
	public boolean isLeq(final ItpZoneState state1, final ItpZoneState state2) {
		return state1.isLeq(state2);
	}

}
