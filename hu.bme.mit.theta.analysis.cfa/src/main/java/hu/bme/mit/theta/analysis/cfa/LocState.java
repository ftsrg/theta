package hu.bme.mit.theta.analysis.cfa;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

public final class LocState<S extends State> implements ExprState {

	private static final int HASH_SEED = 3613;

	private volatile int hashCode = 0;

	private final Loc loc;
	private final S state;

	private LocState(final Loc loc, final S state) {
		this.loc = checkNotNull(loc);
		this.state = checkNotNull(state);
	}

	public static <S extends State> LocState<S> of(final Loc loc, final S state) {
		return new LocState<>(loc, state);
	}

	////

	public Loc getLoc() {
		return loc;
	}

	public S getState() {
		return state;
	}

	////

	public LocState<S> withLoc(final Loc loc) {
		return LocState.of(loc, this.state);
	}

	public <S2 extends State> LocState<S2> withState(final S2 state) {
		return LocState.of(this.loc, state);
	}

	////

	@Override
	public Expr<BoolType> toExpr() {
		// TODO Should be loc = l and toExpr(state)
		if (state instanceof ExprState) {
			return ((ExprState) state).toExpr();
		} else {
			throw new UnsupportedOperationException();
		}
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
		} else if (obj instanceof LocState) {
			final LocState<?> that = (LocState<?>) obj;
			return this.loc.equals(that.loc) && this.state.equals(that.state);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(loc).add(state).toString();
	}

}
