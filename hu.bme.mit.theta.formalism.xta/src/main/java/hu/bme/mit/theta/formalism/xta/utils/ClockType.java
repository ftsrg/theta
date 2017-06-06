package hu.bme.mit.theta.formalism.xta.utils;

import hu.bme.mit.theta.core.Type;

public final class ClockType implements Type {

	private static final ClockType INSTANCE = new ClockType();

	private ClockType() {
	}

	public static ClockType getInstance() {
		return INSTANCE;
	}

	@Override
	public String toString() {
		return "Clock";
	}

}
