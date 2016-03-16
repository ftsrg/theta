package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public abstract class AbstractIntType extends AbstractBaseType implements IntType {

	private static final int HASH_SEED = 222670;

	private static final String TYPE_NAME = "Int";

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
		return TYPE_NAME;
	}

}
