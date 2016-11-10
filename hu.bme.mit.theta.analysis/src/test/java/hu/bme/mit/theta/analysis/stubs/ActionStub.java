package hu.bme.mit.theta.analysis.stubs;

import hu.bme.mit.theta.analysis.Action;

public class ActionStub implements Action {
	private final String label;

	public ActionStub(final String label) {
		this.label = label;
	}

	@Override
	public String toString() {
		return label;
	}
}
