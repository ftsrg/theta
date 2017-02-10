package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.loc.LocState;
import hu.bme.mit.theta.analysis.prod.Prod2State;
import hu.bme.mit.theta.analysis.tcfa.zone.itp.ItpZoneState;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.formalism.tcfa.TcfaEdge;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;

public final class TcfaLawiState implements ExprState {
	private static final int HASH_SEED = 3691;
	private volatile int hashCode = 0;

	private final LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge> state;

	private TcfaLawiState(final LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge> state) {
		this.state = checkNotNull(state);
	}

	static TcfaLawiState create(final LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge> state) {
		return new TcfaLawiState(state);
	}

	LocState<Prod2State<ExplState, ItpZoneState>, TcfaLoc, TcfaEdge> getState() {
		return state;
	}

	////

	@Override
	public Expr<? extends BoolType> toExpr() {
		return state.toExpr();
	}

	////

	public TcfaLoc getLoc() {
		return state.getLoc();
	}

	public ExplState getExplState() {
		return state.getState()._1();
	}

	public ZoneState getConcreteZone() {
		return state.getState()._2().getState();
	}

	public ZoneState getAbstractZone() {
		return state.getState()._2().getInterpolant();
	}

	////

	public TcfaLawiState withAbstractZone(final ZoneState abstractZone) {
		checkNotNull(abstractZone);
		final ItpZoneState itpZoneState = state.getState()._2().withInterpolant(abstractZone);
		final Prod2State<ExplState, ItpZoneState> prodState = state.getState().with2(itpZoneState);
		return create(state.withState(prodState));
	}

	////

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + state.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof TcfaLawiState) {
			final TcfaLawiState that = (TcfaLawiState) obj;
			return this.state.equals(that.state);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(getLoc().getName()).add(getExplState())
				.add(getAbstractZone()).toString();
	}
}
