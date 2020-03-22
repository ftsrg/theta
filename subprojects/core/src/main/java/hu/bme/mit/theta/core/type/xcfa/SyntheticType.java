package hu.bme.mit.theta.xcfa.type;

import hu.bme.mit.theta.core.type.Type;

public class SyntheticType implements Type {

	private static final SyntheticType INSTANCE = new SyntheticType();

	private SyntheticType() { }

	public static SyntheticType getInstance() {
		return INSTANCE;
	}
}
