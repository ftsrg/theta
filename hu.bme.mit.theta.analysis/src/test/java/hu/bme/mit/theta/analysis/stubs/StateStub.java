package hu.bme.mit.theta.analysis.stubs;

import hu.bme.mit.theta.analysis.State;

public class StateStub implements State {
	private final String label;

	public StateStub(final String label) {
		this.label = label;
	}

	@Override
	public String toString() {
		return label;
	}
}
