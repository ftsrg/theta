package hu.bme.mit.theta.analysis.unit;

import hu.bme.mit.theta.analysis.State;

public final class UnitState implements State {

	private static final UnitState INSTANCE = new UnitState();

	private UnitState() {
	}

	public static UnitState getInstance() {
		return INSTANCE;
	}

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

}
