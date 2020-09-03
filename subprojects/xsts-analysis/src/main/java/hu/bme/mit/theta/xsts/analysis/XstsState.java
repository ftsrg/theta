package hu.bme.mit.theta.xsts.analysis;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class XstsState<S extends ExprState> implements ExprState {

	private final S state;
	private final boolean lastActionWasEnv;
	private final boolean initialized;

	private XstsState(S state, boolean lastActionWasEnv, boolean initialized) {
		this.state = state;
		this.lastActionWasEnv = lastActionWasEnv;
		this.initialized = initialized;
	}

	public static <S extends ExprState> XstsState<S> of(final S state, final boolean lastActionWasEnv, final boolean initialized) {
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
		return Utils.lispStringBuilder(getClass().getSimpleName()).aligned().add(initialized ? "post_init" : "pre_init").add(lastActionWasEnv ? "last_env" : "last_internal").body().add(state).toString();
	}
}
