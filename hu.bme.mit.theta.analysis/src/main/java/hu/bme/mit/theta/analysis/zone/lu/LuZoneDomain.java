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
package hu.bme.mit.theta.analysis.zone.lu;

import hu.bme.mit.theta.analysis.Domain;

public final class LuZoneDomain implements Domain<LuZoneState> {
	private static final LuZoneDomain INSTANCE = new LuZoneDomain();

	private LuZoneDomain() {
	}

	public static LuZoneDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final LuZoneState state) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isBottom(final LuZoneState state) {
		return state.isBottom();
	}

	@Override
	public boolean isLeq(final LuZoneState state1, final LuZoneState state2) {
		return state1.isLeq(state2);
	}

}
