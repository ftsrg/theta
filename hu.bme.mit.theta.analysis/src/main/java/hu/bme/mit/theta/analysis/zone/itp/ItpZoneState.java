package hu.bme.mit.theta.analysis.zone.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class ItpZoneState implements ExprState {

	private static final int HASH_SEED = 3361;
	private volatile int hashCode = 0;

	private final ZoneState zone;
	private final ZoneState interpolant;

	private ItpZoneState(final ZoneState zone, final ZoneState interpolant) {
		checkNotNull(zone);
		checkNotNull(interpolant);

		assert zone.isLeq(interpolant);

		this.zone = zone;
		this.interpolant = interpolant;
	}

	public static ItpZoneState of(final ZoneState state, final ZoneState interpolant) {
		return new ItpZoneState(state, interpolant);
	}

	////

	public ZoneState getZone() {
		return zone;
	}

	public ZoneState getInterpolant() {
		return interpolant;
	}

	////

	public boolean isLeq(final ItpZoneState that) {
		return this.interpolant.isLeq(that.interpolant);
	}

	////

	public ItpZoneState withState(final ZoneState state) {
		return ItpZoneState.of(state, this.interpolant);
	}

	public ItpZoneState withInterpolant(final ZoneState interpolant) {
		return ItpZoneState.of(this.zone, interpolant);
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
			result = 37 * result + zone.hashCode();
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
			return this.zone.equals(that.zone) && this.interpolant.equals(that.interpolant);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return interpolant.toString();
	}

}
