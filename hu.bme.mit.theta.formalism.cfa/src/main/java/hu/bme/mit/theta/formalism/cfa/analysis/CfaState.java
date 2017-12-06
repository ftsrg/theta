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
package hu.bme.mit.theta.formalism.cfa.analysis;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public final class CfaState<S extends ExprState> implements ExprState {

	private static final int HASH_SEED = 3613;
	private volatile int hashCode = 0;

	private final Loc loc;
	private final S state;

	private CfaState(final Loc loc, final S state) {
		this.loc = checkNotNull(loc);
		this.state = checkNotNull(state);
	}

	public static <S extends ExprState> CfaState<S> of(final Loc loc, final S state) {
		return new CfaState<>(loc, state);
	}

	////

	public Loc getLoc() {
		return loc;
	}

	public S getState() {
		return state;
	}

	////

	public CfaState<S> withLoc(final Loc loc) {
		return CfaState.of(loc, this.state);
	}

	public <S2 extends ExprState> CfaState<S2> withState(final S2 state) {
		return CfaState.of(this.loc, state);
	}

	////

	@Override
	public boolean isBottom() {
		return state.isBottom();
	}

	@Override
	public Expr<BoolType> toExpr() {
		// TODO Should be loc = l and toExpr(state)
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
		} else if (obj instanceof CfaState) {
			final CfaState<?> that = (CfaState<?>) obj;
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
