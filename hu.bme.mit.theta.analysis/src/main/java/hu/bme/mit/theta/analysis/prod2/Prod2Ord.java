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
package hu.bme.mit.theta.analysis.prod2;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;

final class Prod2Ord<S1 extends State, S2 extends State> implements PartialOrd<Prod2State<S1, S2>> {

	private final PartialOrd<S1> partialOrd1;
	private final PartialOrd<S2> partialOrd2;

	private Prod2Ord(final PartialOrd<S1> partialOrd1, final PartialOrd<S2> partialOrd2) {
		this.partialOrd1 = checkNotNull(partialOrd1);
		this.partialOrd2 = checkNotNull(partialOrd2);
	}

	public static <S1 extends State, S2 extends State> Prod2Ord<S1, S2> create(final PartialOrd<S1> partialOrd1,
			final PartialOrd<S2> partialOrd2) {
		return new Prod2Ord<>(partialOrd1, partialOrd2);
	}

	@Override
	public boolean isLeq(final Prod2State<S1, S2> state1, final Prod2State<S1, S2> state2) {
		if (state1.isBottom()) {
			return true;
		} else if (state2.isBottom()) {
			return false;
		} else {
			return partialOrd1.isLeq(state1._1(), state2._1()) && partialOrd2.isLeq(state1._2(), state2._2());
		}
	}

}
