/*
 *  Copyright 2018 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xta.analysis.expl.itp;

import hu.bme.mit.theta.analysis.PartialOrd;

final class ItpExplOrd implements PartialOrd<ItpExplState> {

	private ItpExplOrd() {
	}

	private static final class LazyHolder {
		private static final ItpExplOrd INSTANCE = new ItpExplOrd();
	}

	public static ItpExplOrd getInstance() {
		return LazyHolder.INSTANCE;
	}

	@Override
	public boolean isLeq(final ItpExplState state1, final ItpExplState state2) {
		if (state1.isBottom()) {
			return true;
		} else if (state2.isBottom()) {
			return false;
		} else {
			return state1.getAbstrState().isLeq(state2.getAbstrState());
		}
	}

}
