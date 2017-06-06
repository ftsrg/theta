package hu.bme.mit.theta.core.type.booltype;

import hu.bme.mit.theta.core.Type;

public final class BoolType implements Type {
	private static final BoolType INSTANCE = new BoolType();
	private static final int HASH_SEED = 754364;
	private static final String TYPE_LABEL = "Bool";

	private BoolType() {
	}

	static BoolType getInstance() {
		return INSTANCE;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return obj instanceof BoolType;
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}

}
