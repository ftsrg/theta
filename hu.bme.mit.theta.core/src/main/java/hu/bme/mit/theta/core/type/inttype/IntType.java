package hu.bme.mit.theta.core.type.inttype;

import hu.bme.mit.theta.core.Type;

public final class IntType implements Type {
	private static final IntType INSTANCE = new IntType();
	private static final int HASH_SEED = 222670;
	private static final String TYPE_LABEL = "Int";

	private IntType() {
	}

	static IntType getInstance() {
		return INSTANCE;
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof IntType);
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}

}
