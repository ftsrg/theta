package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public class XstsState<S extends ExprState> implements ExprState {

    private static final int HASH_SEED = 4413;
    private volatile int hashCode = 0;

    private final S state;
    private final boolean lastActionWasEnv;

        private XstsState(S state, boolean lastActionWasEnv) {
        this.state = state;
        this.lastActionWasEnv = lastActionWasEnv;
    }

    public static <S extends ExprState> XstsState<S> of(final S state, final boolean lastActionWasEnv) {
        return new XstsState<>(state, lastActionWasEnv);
    }

    public S getState() {
        return state;
    }

    public boolean lastActionWasEnv() {
        return lastActionWasEnv;
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
        return Utils.lispStringBuilder(getClass().getSimpleName()).aligned().add(lastActionWasEnv?"ENV":"INTERNAL").body().add(state).toString();
    }
}
