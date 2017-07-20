package hu.bme.mit.theta.analysis.zone.act;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Set;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.rattype.RatType;

public final class ActZoneState implements ExprState {
	private static final int HASH_SEED = 7253;

	private final ZoneState zone;
	private final Set<VarDecl<RatType>> activeVars;

	private volatile int hashCode = 0;
	@SuppressWarnings("unused")
	private volatile Expr<BoolType> expr = null;

	public ActZoneState(final ZoneState zone, final Iterable<? extends VarDecl<RatType>> activeVars) {
		this.zone = checkNotNull(zone);
		this.activeVars = ImmutableSet.copyOf(checkNotNull(activeVars));
	}

	public static ActZoneState of(final ZoneState zone, final Iterable<? extends VarDecl<RatType>> activeVars) {
		return new ActZoneState(zone, activeVars);
	}

	public ZoneState getZone() {
		return zone;
	}

	public Set<VarDecl<RatType>> getActiveVars() {
		return activeVars;
	}

	public ActZoneState withActiveVars(final Iterable<? extends VarDecl<RatType>> activeVars) {
		return ActZoneState.of(zone, activeVars);
	}

	public boolean isBottom() {
		return zone.isBottom();
	}

	public boolean isLeq(final ActZoneState that) {
		return this.activeVars.containsAll(that.activeVars) && this.zone.isLeq(that.zone, that.activeVars);
	}

	@Override
	public Expr<BoolType> toExpr() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + zone.hashCode();
			result = 31 * result + activeVars.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ActZoneState) {
			final ActZoneState that = (ActZoneState) obj;
			return this.zone.equals(that.zone) && this.activeVars.equals(that.activeVars);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringJoiner sj = new StringJoiner("\n");
		sj.add(zone.toString());
		sj.add("active vars:");
		activeVars.forEach(c -> sj.add(c.getName()));
		return sj.toString();
	}

}
