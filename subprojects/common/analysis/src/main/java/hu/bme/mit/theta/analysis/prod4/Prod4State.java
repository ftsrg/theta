/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import java.util.ArrayList;
import java.util.Collection;

public abstract class Prod4State<
                S1 extends State, S2 extends State, S3 extends State, S4 extends State>
        implements ExprState {

    private Prod4State() {}

    public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            Prod4State<S1, S2, S3, S4> of(
                    final S1 state1, final S2 state2, final S3 state3, final S4 state4) {
        checkNotNull(state1);
        checkNotNull(state2);
        checkNotNull(state3);
        checkNotNull(state4);
        if (state1.isBottom()) {
            return bottom1(state1);
        } else if (state2.isBottom()) {
            return bottom2(state2);
        } else if (state3.isBottom()) {
            return bottom3(state3);
        } else if (state4.isBottom()) {
            return bottom4(state4);
        } else {
            return product(state1, state2, state3, state4);
        }
    }

    public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            Prod4State<S1, S2, S3, S4> bottom1(final S1 state) {
        return new Bottom1<>(state);
    }

    public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            Prod4State<S1, S2, S3, S4> bottom2(final S2 state) {
        return new Bottom2<>(state);
    }

    public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            Prod4State<S1, S2, S3, S4> bottom3(final S3 state) {
        return new Bottom3<>(state);
    }

    public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            Prod4State<S1, S2, S3, S4> bottom4(final S4 state) {
        return new Bottom4<>(state);
    }

    private static <S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            Prod4State<S1, S2, S3, S4> product(
                    final S1 state1, final S2 state2, final S3 state3, final S4 state4) {
        return new Product<>(state1, state2, state3, state4);
    }

    public static <S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            Collection<Prod4State<S1, S2, S3, S4>> cartesian(
                    final Iterable<? extends S1> states1,
                    final Iterable<? extends S2> states2,
                    final Iterable<? extends S3> states3,
                    final Iterable<? extends S4> states4) {
        final Collection<Prod4State<S1, S2, S3, S4>> result = new ArrayList<>();
        for (final S1 state1 : states1) {
            for (final S2 state2 : states2) {
                for (final S3 state3 : states3) {
                    for (final S4 state4 : states4) {
                        result.add(product(state1, state2, state3, state4));
                    }
                }
            }
        }
        return result;
    }

    public abstract S1 getState1();

    public abstract S2 getState2();

    public abstract S3 getState3();

    public abstract S4 getState4();

    public abstract boolean isBottom1();

    public abstract boolean isBottom2();

    public abstract boolean isBottom3();

    public abstract boolean isBottom4();

    public abstract <S extends State> Prod4State<S, S2, S3, S4> with1(final S state);

    public abstract <S extends State> Prod4State<S1, S, S3, S4> with2(final S state);

    public abstract <S extends State> Prod4State<S1, S2, S, S4> with3(final S state);

    public abstract <S extends State> Prod4State<S1, S2, S3, S> with4(final S state);

    private static final class Product<
                    S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            extends Prod4State<S1, S2, S3, S4> {

        private static final int HASH_SEED = 2297;
        private volatile int hashCode = 0;

        private final S1 state1;
        private final S2 state2;
        private final S3 state3;
        private final S4 state4;

        private Product(final S1 state1, final S2 state2, final S3 state3, final S4 state4) {
            checkNotNull(state1);
            checkNotNull(state2);
            checkNotNull(state3);
            checkNotNull(state4);
            checkArgument(!state1.isBottom());
            checkArgument(!state2.isBottom());
            checkArgument(!state3.isBottom());
            checkArgument(!state4.isBottom());
            this.state1 = state1;
            this.state2 = state2;
            this.state3 = state3;
            this.state4 = state4;
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
        public S3 getState3() {
            return state3;
        }

        @Override
        public S4 getState4() {
            return state4;
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
        public boolean isBottom3() {
            return false;
        }

        @Override
        public boolean isBottom4() {
            return false;
        }

        @Override
        public <S extends State> Prod4State<S, S2, S3, S4> with1(final S state) {
            if (state.isBottom()) {
                return bottom1(state);
            } else {
                return product(state, state2, state3, state4);
            }
        }

        @Override
        public <S extends State> Prod4State<S1, S, S3, S4> with2(final S state) {
            if (state.isBottom()) {
                return bottom2(state);
            } else {
                return product(state1, state, state3, state4);
            }
        }

        @Override
        public <S extends State> Prod4State<S1, S2, S, S4> with3(final S state) {
            if (state.isBottom()) {
                return bottom3(state);
            } else {
                return product(state1, state2, state, state4);
            }
        }

        @Override
        public <S extends State> Prod4State<S1, S2, S3, S> with4(final S state) {
            if (state.isBottom()) {
                return bottom4(state);
            } else {
                return product(state1, state2, state3, state);
            }
        }

        @Override
        public boolean isBottom() {
            return false;
        }

        @Override
        public Expr<BoolType> toExpr() {
            if (state1 instanceof ExprState
                    && state2 instanceof ExprState
                    && state3 instanceof ExprState) {
                final ExprState exprState1 = (ExprState) state1;
                final ExprState exprState2 = (ExprState) state2;
                final ExprState exprState3 = (ExprState) state3;
                final ExprState exprState4 = (ExprState) state4;
                return And(
                        exprState1.toExpr(),
                        exprState2.toExpr(),
                        exprState3.toExpr(),
                        exprState4.toExpr());
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
                result = 37 * result + state3.hashCode();
                result = 37 * result + state4.hashCode();
                hashCode = result;
            }
            return result;
        }

        @Override
        public boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            } else if (obj != null && this.getClass() == obj.getClass()) {
                final Product<?, ?, ?, ?> that = (Product<?, ?, ?, ?>) obj;
                return this.state1.equals(that.state1)
                        && this.state2.equals(that.state2)
                        && this.state3.equals(that.state3)
                        && this.state4.equals(that.state4);
            } else {
                return false;
            }
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(Prod4State.class.getSimpleName())
                    .body()
                    .add(state1)
                    .add(state2)
                    .add(state3)
                    .add(state4)
                    .toString();
        }
    }

    private abstract static class Bottom<
                    S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            extends Prod4State<S1, S2, S3, S4> {

        private static final int HASH_SEED = 4129;
        private volatile int hashCode = 0;

        private Bottom() {}

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
                hashCode = result;
            }
            return result;
        }

        @Override
        public final boolean equals(final Object obj) {
            if (this == obj) {
                return true;
            } else if (obj != null && this.getClass() == obj.getClass()) {
                final Bottom<?, ?, ?, ?> that = (Bottom<?, ?, ?, ?>) obj;
                return this.getIndex() == that.getIndex()
                        && this.getState().equals(that.getState());
            } else {
                return false;
            }
        }

        @Override
        public final String toString() {
            return Utils.lispStringBuilder(Prod4State.class.getSimpleName())
                    .add(getIndex())
                    .add(getState())
                    .toString();
        }
    }

    private static final class Bottom1<
                    S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            extends Bottom<S1, S2, S3, S4> {

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
        public S3 getState3() {
            throw new UnsupportedOperationException();
        }

        @Override
        public S4 getState4() {
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
        public boolean isBottom3() {
            return false;
        }

        @Override
        public boolean isBottom4() {
            return false;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S, S2, S3, S4> with1(final S state) {
            checkArgument(state.isBottom());
            return (Prod4State<S, S2, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S, S3, S4> with2(final S state) {
            return (Prod4State<S1, S, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S, S4> with3(final S state) {
            return (Prod4State<S1, S2, S, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S3, S> with4(final S state) {
            return (Prod4State<S1, S2, S3, S>) this;
        }
    }

    private static final class Bottom2<
                    S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            extends Bottom<S1, S2, S3, S4> {

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
        public S3 getState3() {
            throw new UnsupportedOperationException();
        }

        @Override
        public S4 getState4() {
            throw new UnsupportedOperationException();
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
        public boolean isBottom3() {
            return false;
        }

        @Override
        public boolean isBottom4() {
            return false;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S, S2, S3, S4> with1(final S state) {
            return (Prod4State<S, S2, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S, S3, S4> with2(final S state) {
            checkArgument(state.isBottom());
            return (Prod4State<S1, S, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S, S4> with3(final S state) {
            return (Prod4State<S1, S2, S, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S3, S> with4(final S state) {
            return (Prod4State<S1, S2, S3, S>) this;
        }
    }

    private static final class Bottom3<
                    S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            extends Bottom<S1, S2, S3, S4> {

        private final S3 state;

        public Bottom3(final S3 state) {
            checkNotNull(state);
            checkArgument(state.isBottom());
            this.state = state;
        }

        @Override
        public int getIndex() {
            return 3;
        }

        @Override
        public S3 getState() {
            return state;
        }

        @Override
        public S1 getState1() {
            throw new UnsupportedOperationException();
        }

        @Override
        public S2 getState2() {
            throw new UnsupportedOperationException();
        }

        @Override
        public S3 getState3() {
            return state;
        }

        @Override
        public S4 getState4() {
            throw new UnsupportedOperationException();
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
        public boolean isBottom3() {
            return true;
        }

        @Override
        public boolean isBottom4() {
            return false;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S, S2, S3, S4> with1(final S state) {
            return (Prod4State<S, S2, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S, S3, S4> with2(final S state) {
            return (Prod4State<S1, S, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S, S4> with3(final S state) {
            checkArgument(state.isBottom());
            return (Prod4State<S1, S2, S, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S3, S> with4(final S state) {
            return (Prod4State<S1, S2, S3, S>) this;
        }
    }

    private static final class Bottom4<
                    S1 extends State, S2 extends State, S3 extends State, S4 extends State>
            extends Bottom<S1, S2, S3, S4> {

        private final S4 state;

        public Bottom4(final S4 state) {
            checkNotNull(state);
            checkArgument(state.isBottom());
            this.state = state;
        }

        @Override
        public int getIndex() {
            return 4;
        }

        @Override
        public S4 getState() {
            return state;
        }

        @Override
        public S1 getState1() {
            throw new UnsupportedOperationException();
        }

        @Override
        public S2 getState2() {
            throw new UnsupportedOperationException();
        }

        @Override
        public S3 getState3() {
            throw new UnsupportedOperationException();
        }

        @Override
        public S4 getState4() {
            return state;
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
        public boolean isBottom3() {
            return false;
        }

        @Override
        public boolean isBottom4() {
            return true;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S, S2, S3, S4> with1(final S state) {
            return (Prod4State<S, S2, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S, S3, S4> with2(final S state) {
            return (Prod4State<S1, S, S3, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S, S4> with3(final S state) {
            return (Prod4State<S1, S2, S, S4>) this;
        }

        @Override
        @SuppressWarnings("unchecked")
        public <S extends State> Prod4State<S1, S2, S3, S> with4(final S state) {
            checkArgument(state.isBottom());
            return (Prod4State<S1, S2, S3, S>) this;
        }
    }
}
