package hu.bme.mit.theta.analysis.stubs;

import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;

public class DomainStub implements Domain<State> {

	@Override
	public boolean isTop(final State state) {
		return false;
	}

	@Override
	public boolean isBottom(final State state) {
		return false;
	}

	@Override
	public boolean isLeq(final State state1, final State state2) {
		return state1.equals(state2);
	}

}
