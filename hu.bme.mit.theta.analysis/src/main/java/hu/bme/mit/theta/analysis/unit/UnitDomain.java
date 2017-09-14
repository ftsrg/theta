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
package hu.bme.mit.theta.analysis.unit;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Domain;

final class UnitDomain implements Domain<UnitState> {

	private static final UnitDomain INSTANCE = new UnitDomain();

	private UnitDomain() {
	}

	public static UnitDomain getInstance() {
		return INSTANCE;
	}

	@Override
	public boolean isTop(final UnitState state) {
		checkNotNull(state);
		return true;
	}

	@Override
	public boolean isBottom(final UnitState state) {
		checkNotNull(state);
		return false;
	}

	@Override
	public boolean isLeq(final UnitState state1, final UnitState state2) {
		checkNotNull(state1);
		checkNotNull(state2);
		return true;
	}

}
