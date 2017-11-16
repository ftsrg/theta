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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public abstract class Prod2State<S1 extends State, S2 extends State> implements ExprState {

	private Prod2State() {
	}

	public static <S1 extends State, S2 extends State> Prod2State<S1, S2> of(final S1 state1, final S2 state2) {
		checkNotNull(state1);
		checkNotNull(state2);
		if (state1.isBottom()) {
			return bottom1(state1);
		} else if (state2.isBottom()) {
			return bottom2(state2);
		} else {
			return product(state1, state2);
		}
	}

	public static <S1 extends State, S2 extends State> Prod2State<S1, S2> bottom1(final S1 state) {
		return new Bottom1<>(state);
	}

	public static <S1 extends State, S2 extends State> Prod2State<S1, S2> bottom2(final S2 state) {
		return new Bottom2<>(state);
	}

	private static <S1 extends State, S2 extends State> Prod2State<S1, S2> product(final S1 state1, final S2 state2) {
		return new Product<>(state1, state2);
	}

	public static <S1 extends State, S2 extends State> Collection<Prod2State<S1, S2>> cartesian(
			final Iterable<? extends S1> states1, final Iterable<? extends S2> states2) {
		final Collection<Prod2State<S1, S2>> result = new ArrayList<>();
		for (final S1 state1 : states1) {
			for (final S2 state2 : states2) {
				result.add(product(state1, state2));
			}
		}
		return result;
	}

	public abstract S1 getState1();

	public abstract S2 getState2();

	public abstract boolean isBottom1();

	public abstract boolean isBottom2();

	public abstract <S extends State> Prod2State<S, S2> with1(final S state);

	public abstract <S extends State> Prod2State<S1, S> with2(final S state);

	private static final class Product<S1 extends State, S2 extends State> extends Prod2State<S1, S2> {
		private static final int HASH_SEED = 7879;
		private volatile int hashCode = 0;

		private final S1 state1;
		private final S2 state2;

		private Product(final S1 state1, final S2 state2) {
			checkNotNull(state1);
			checkNotNull(state2);
			checkArgument(!state1.isBottom());
			checkArgument(!state2.isBottom());
			this.state1 = state1;
			this.state2 = state2;
		}

		@Override
		public S1 getState1() {
			return state1;
		}

		@Override
		public S2 getState2() {
			return state2;
		}

		@Override
		public boolean isBottom1() {
			return false;
		}

		@Override
		public boolean isBottom2() {
			return false;
		}

		@Override
		public <S extends State> Prod2State<S, S2> with1(final S state) {
			if (state.isBottom()) {
				return bottom1(state);
			} else {
				return product(state, state2);
			}
		}

		@Override
		public <S extends State> Prod2State<S1, S> with2(final S state) {
			if (state.isBottom()) {
				return bottom2(state);
			} else {
				return product(state1, state);
			}
		}

		@Override
		public boolean isBottom() {
			return false;
		}

		@Override
		public Expr<BoolType> toExpr() {
			if (state1 instanceof ExprState && state2 instanceof ExprState) {
				final ExprState exprState1 = (ExprState) state1;
				final ExprState exprState2 = (ExprState) state2;
				return And(exprState1.toExpr(), exprState2.toExpr());
			} else {
				throw new UnsupportedOperationException();
			}
		}

		@Override
		public int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 37 * result + state1.hashCode();
				result = 37 * result + state2.hashCode();
				result = hashCode;
			}
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof Product) {
				final Product<?, ?> that = (Product<?, ?>) obj;
				return this.state1.equals(that.state1) && this.state2.equals(that.state2);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return state1.toString() + " " + state2.toString();
		}
	}

	private static abstract class Bottom<S1 extends State, S2 extends State> extends Prod2State<S1, S2> {
		private static final int HASH_SEED = 2879;
		private volatile int hashCode = 0;

		private Bottom() {
		}

		public abstract int getIndex();

		public abstract State getState();

		@Override
		public final boolean isBottom() {
			return true;
		}

		@Override
		public final Expr<BoolType> toExpr() {
			final State state = getState();
			if (state instanceof ExprState) {
				final ExprState exprState = (ExprState) state;
				return exprState.toExpr();
			} else {
				throw new UnsupportedOperationException();
			}
		}

		@Override
		public final int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 37 * result + getIndex();
				result = 37 * result + getState().hashCode();
				result = hashCode;
			}
			return result;
		}

		@Override
		public final boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof Bottom) {
				final Bottom<?, ?> that = (Bottom<?, ?>) obj;
				return this.getIndex() == that.getIndex() && this.getState().equals(that.getState());
			} else {
				return false;
			}
		}

		@Override
		public final String toString() {
			return getState().toString();
		}
	}

	private static final class Bottom1<S1 extends State, S2 extends State> extends Bottom<S1, S2> {
		private final S1 state;

		private Bottom1(final S1 state) {
			checkNotNull(state);
			checkArgument(state.isBottom());
			this.state = state;
		}

		@Override
		public int getIndex() {
			return 1;
		}

		@Override
		public S1 getState() {
			return state;
		}

		@Override
		public S1 getState1() {
			return state;
		}

		@Override
		public S2 getState2() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isBottom1() {
			return true;
		}

		@Override
		public boolean isBottom2() {
			return false;
		}

		@Override
		@SuppressWarnings("unchecked")
		public <S extends State> Prod2State<S, S2> with1(final S state) {
			checkArgument(state.isBottom());
			return (Prod2State<S, S2>) this;
		}

		@Override
		@SuppressWarnings("unchecked")
		public <S extends State> Prod2State<S1, S> with2(final S state) {
			return (Prod2State<S1, S>) this;
		}
	}

	private static final class Bottom2<S1 extends State, S2 extends State> extends Bottom<S1, S2> {
		private final S2 state;

		public Bottom2(final S2 state) {
			checkNotNull(state);
			checkArgument(state.isBottom());
			this.state = state;
		}

		@Override
		public int getIndex() {
			return 2;
		}

		@Override
		public S2 getState() {
			return state;
		}

		@Override
		public S1 getState1() {
			throw new UnsupportedOperationException();
		}

		@Override
		public S2 getState2() {
			return state;
		}

		@Override
		public boolean isBottom1() {
			return false;
		}

		@Override
		public boolean isBottom2() {
			return true;
		}

		@Override
		@SuppressWarnings("unchecked")
		public <S extends State> Prod2State<S, S2> with1(final S state) {
			return (Prod2State<S, S2>) this;
		}

		@Override
		@SuppressWarnings("unchecked")
		public <S extends State> Prod2State<S1, S> with2(final S state) {
			checkArgument(state.isBottom());
			return (Prod2State<S1, S>) this;
		}
	}

}
