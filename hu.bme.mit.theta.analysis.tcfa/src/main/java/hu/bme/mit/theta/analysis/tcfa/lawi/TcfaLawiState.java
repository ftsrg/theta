package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.composite.CompositeState;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.tcfa.TcfaState;
import hu.bme.mit.theta.analysis.zone.ZoneState;

final class TcfaLawiState implements State {

	private final TcfaState<CompositeState<ZoneState, ExplState>> state;

	private TcfaLawiState(final TcfaState<CompositeState<ZoneState, ExplState>> state) {
		this.state = checkNotNull(state);
	}

	public static TcfaLawiState create(final TcfaState<CompositeState<ZoneState, ExplState>> state) {
		return new TcfaLawiState(state);
	}

	public TcfaState<CompositeState<ZoneState, ExplState>> getState() {
		return state;
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public String toString() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

}
