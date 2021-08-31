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
package hu.bme.mit.theta.xcfa.analysis;

import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.MultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.StackableExprState;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaOrd<S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>> implements PartialOrd<XcfaState<S, SS, SSS>> {

	private final PartialOrd<S> partialOrd;

	private XcfaOrd(final PartialOrd<S> partialOrd) {
		this.partialOrd = checkNotNull(partialOrd);
	}

	public static <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>> XcfaOrd<S, SS, SSS> create(final PartialOrd<S> partialOrd) {
		return new XcfaOrd<>(partialOrd);
	}

	@Override
	public boolean isLeq(final XcfaState<S, SS, SSS> state1, final XcfaState<S, SS, SSS> state2) {
		return state1.getLocations().equals(state2.getLocations()) && state1.getState().getStates().entrySet().stream().allMatch(entry -> partialOrd.isLeq(entry.getValue().peek().getState(), state2.getState().getStates().get(entry.getKey()).peek().getState()));
	}

}
