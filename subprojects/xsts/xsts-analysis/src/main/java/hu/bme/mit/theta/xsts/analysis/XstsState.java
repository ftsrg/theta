/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.Objects;

public final class XstsState<S extends ExprState> implements ExprState {

    private final S state;
    private final boolean lastActionWasEnv;
    private final boolean initialized;

    private XstsState(S state, boolean lastActionWasEnv, boolean initialized) {
        this.state = state;
        this.lastActionWasEnv = lastActionWasEnv;
        this.initialized = initialized;
    }

    public static <S extends ExprState> XstsState<S> of(final S state,
                                                        final boolean lastActionWasEnv, final boolean initialized) {
        return new XstsState<>(state, lastActionWasEnv, initialized);
    }

    public S getState() {
        return state;
    }

    public boolean lastActionWasEnv() {
        return lastActionWasEnv;
    }

    public boolean isInitialized() {
        return initialized;
    }

    @Override
    public Expr<BoolType> toExpr() {
        return state.toExpr();
    }

    @Override
    public boolean isBottom() {
        return state.isBottom();
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).aligned()
                .add(initialized ? "post_init" : "pre_init")
                .add(lastActionWasEnv ? "last_env" : "last_internal").body().add(state).toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        XstsState<?> xstsState = (XstsState<?>) o;
        return lastActionWasEnv == xstsState.lastActionWasEnv
                && initialized == xstsState.initialized && state.equals(xstsState.state);
    }

    @Override
    public int hashCode() {
        return Objects.hash(state, lastActionWasEnv, initialized);
    }
}
