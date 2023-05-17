/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.analysis.impl.singlethread;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.xcfa.analysis.common.XcfaState;

import static com.google.common.base.Preconditions.checkNotNull;

public class XcfaSTOrd<S extends ExprState> implements PartialOrd<XcfaState<S>> {

	private final PartialOrd<S> partialOrd;

	private XcfaSTOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState> XcfaSTOrd<S> create(final PartialOrd<S> partialOrd) {
		return new XcfaSTOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(final XcfaState<S> state1, final XcfaState<S> state2) {
		return ((XcfaSTState<S>) state1).equalLocations(((XcfaSTState<S>) state2))
				&& partialOrd.isLeq(state1.getGlobalState(), state2.getGlobalState());
	}
}
