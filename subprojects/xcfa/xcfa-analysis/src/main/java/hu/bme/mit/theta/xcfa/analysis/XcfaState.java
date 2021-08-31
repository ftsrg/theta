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

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.MultiStackableExprState;
import hu.bme.mit.theta.analysis.expr.StackableExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaState<S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>> implements ExprState {

	private static final int HASH_SEED = 3614;
	private volatile int hashCode = 0;

	private final SSS state;

	private XcfaState(final SSS state) {
		this.state = checkNotNull(state);
	}

	public static <S extends ExprState, SS extends StackableExprState<XcfaLocationState<S>>, SSS extends MultiStackableExprState<Integer, XcfaLocationState<S>, SS>> XcfaState<S, SS, SSS> of(final SSS state) {
		return new XcfaState<>(state);
	}

	////

	public SSS getState() {
		return state;
	}

	////

	public <S2 extends ExprState, SS2 extends StackableExprState<XcfaLocationState<S2>>, SSS2 extends MultiStackableExprState<Integer, XcfaLocationState<S2>, SS2>> XcfaState<S2, SS2, SSS2> withState(final SSS2 state) {
		return XcfaState.of(state);
	}

	////

	@Override
	public boolean isBottom() {
		return state.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		return state.toExpr();
	}

	public boolean isErrorState() {
		return state.getStates().values().stream().anyMatch(ss -> ss.getStates().stream().anyMatch(sXcfaLocationState -> sXcfaLocationState.getLoc().isErrorLoc()));
	}

	public Map<Integer, XcfaLocation> getLocations() {
		return state.getStates().entrySet().stream().map(t -> Map.entry(t.getKey(), t.getValue().peek().getLoc())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + state.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XcfaState) {
			final XcfaState<?, ?, ?> that = (XcfaState<?, ?, ?>) obj;
			return this.state.equals(that.state);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return state.toString();
	}

}
