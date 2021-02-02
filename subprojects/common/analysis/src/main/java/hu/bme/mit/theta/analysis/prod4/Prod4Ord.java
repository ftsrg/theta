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
package hu.bme.mit.theta.analysis.prod4;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;

final class Prod4Ord<S1 extends State, S2 extends State, S3 extends State, S4 extends State>
		implements PartialOrd<Prod4State<S1, S2, S3, S4>> {

	private final PartialOrd<S1> partialOrd1;
	private final PartialOrd<S2> partialOrd2;
	private final PartialOrd<S3> partialOrd3;
	private final PartialOrd<S4> partialOrd4;

	private Prod4Ord(final PartialOrd<S1> partialOrd1, final PartialOrd<S2> partialOrd2,
					 final PartialOrd<S3> partialOrd3, final PartialOrd<S4> partialOrd4) {
		this.partialOrd1 = checkNotNull(partialOrd1);
		this.partialOrd2 = checkNotNull(partialOrd2);
		this.partialOrd3 = checkNotNull(partialOrd3);
		this.partialOrd4 = checkNotNull(partialOrd4);
	}

	public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State> Prod4Ord<S1, S2, S3, S4> create(
			final PartialOrd<S1> partialOrd1, final PartialOrd<S2> partialOrd2, final PartialOrd<S3> partialOrd3,
			final PartialOrd<S4> partialOrd4) {
		return new Prod4Ord<>(partialOrd1, partialOrd2, partialOrd3, partialOrd4);
	}

	@Override
	public boolean isLeq(final Prod4State<S1, S2, S3, S4> state1, final Prod4State<S1, S2, S3, S4> state2) {
		if (state1.isBottom()) {
			return true;
		} else if (state2.isBottom()) {
			return false;
		} else {
			return partialOrd1.isLeq(state1.getState1(), state2.getState1())
					&& partialOrd2.isLeq(state1.getState2(), state2.getState2())
					&& partialOrd3.isLeq(state1.getState3(), state2.getState3())
					&& partialOrd4.isLeq(state1.getState4(), state2.getState4());
		}
	}

}
