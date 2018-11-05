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
package hu.bme.mit.theta.analysis.prod3;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;

final class Prod3Ord<S1 extends State, S2 extends State, S3 extends State>
		implements PartialOrd<Prod3State<S1, S2, S3>> {

	private final PartialOrd<S1> partialOrd1;
	private final PartialOrd<S2> partialOrd2;
	private final PartialOrd<S3> partialOrd3;

	private Prod3Ord(final PartialOrd<S1> partialOrd1, final PartialOrd<S2> partialOrd2,
			final PartialOrd<S3> partialOrd3) {
		this.partialOrd1 = checkNotNull(partialOrd1);
		this.partialOrd2 = checkNotNull(partialOrd2);
		this.partialOrd3 = checkNotNull(partialOrd3);
	}

	public static <S1 extends State, S2 extends State, S3 extends State> Prod3Ord<S1, S2, S3> create(
			final PartialOrd<S1> partialOrd1, final PartialOrd<S2> partialOrd2, final PartialOrd<S3> partialOrd3) {
		return new Prod3Ord<>(partialOrd1, partialOrd2, partialOrd3);
	}

	@Override
	public boolean isLeq(final Prod3State<S1, S2, S3> state1, final Prod3State<S1, S2, S3> state2) {
		if (state1.isBottom()) {
			return true;
		} else if (state2.isBottom()) {
			return false;
		} else {
			return partialOrd1.isLeq(state1.getState1(), state2.getState1())
					&& partialOrd2.isLeq(state1.getState2(), state2.getState2())
					&& partialOrd3.isLeq(state1.getState3(), state2.getState3());
		}
	}

}
