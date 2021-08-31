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
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;

import static com.google.common.base.Preconditions.checkNotNull;

public final class XcfaLocationState<S extends ExprState> implements ExprState {

	private static final int HASH_SEED = 3615;
	private volatile int hashCode = 0;

	private final XcfaLocation loc;
	private final S state;

	private XcfaLocationState(final XcfaLocation loc, final S state) {
		this.loc = checkNotNull(loc);
		this.state = checkNotNull(state);
	}

	public static <S extends ExprState> XcfaLocationState<S> of(final XcfaLocation loc, final S state) {
		return new XcfaLocationState<>(loc, state);
	}

	////


	public XcfaLocation getLoc() {
		return loc;
	}

	public S getState() {
		return state;
	}

	////

	public XcfaLocationState<S> withLoc(final XcfaLocation loc) {
		return XcfaLocationState.of(loc, this.state);
	}

	public <S2 extends ExprState> XcfaLocationState<S2> withState(final S2 state) {
		return XcfaLocationState.of(this.loc, state);
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

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + loc.hashCode();
			result = 31 * result + state.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof XcfaLocationState) {
			final XcfaLocationState<?> that = (XcfaLocationState<?>) obj;
			return this.loc.equals(that.loc) && this.state.equals(that.state);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).add(loc.getName()).body().add(state).toString();
	}

}
