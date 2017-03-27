package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;

public final class ItpZoneState implements ExprState {

	private static final int HASH_SEED = 3361;
	private volatile int hashCode = 0;

	private final ZoneState state;
	private final ZoneState interpolant;

	private ItpZoneState(final ZoneState state, final ZoneState interpolant) {
		checkNotNull(state);
		checkNotNull(interpolant);
		checkArgument(state.isLeq(interpolant));
		this.state = state;
		this.interpolant = interpolant;
	}

	public static ItpZoneState of(final ZoneState state, final ZoneState interpolant) {
		return new ItpZoneState(state, interpolant);
	}

	////

	public ZoneState getState() {
		return state;
	}

	public ZoneState getInterpolant() {
		return interpolant;
	}

	////

	public ItpZoneState withState(final ZoneState state) {
		return ItpZoneState.of(state, this.interpolant);
	}

	public ItpZoneState withInterpolant(final ZoneState interpolant) {
		return ItpZoneState.of(this.state, interpolant);
	}

	////

	@Override
	public Expr<? extends BoolType> toExpr() {
		return interpolant.toExpr();
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 37 * result + state.hashCode();
			result = 37 * result + interpolant.hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ItpZoneState) {
			final ItpZoneState that = (ItpZoneState) obj;
			return this.state.equals(that.state) && this.interpolant.equals(that.interpolant);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(this.getClass().getSimpleName()).add(state).add(interpolant).toString();
	}

}
