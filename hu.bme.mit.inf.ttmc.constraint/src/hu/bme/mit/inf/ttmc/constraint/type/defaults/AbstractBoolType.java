package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public abstract class AbstractBoolType extends AbstractBaseType implements BoolType {

	private static final int HASH_SEED = 754364;

	private static final String TYPE_NAME = "Bool";

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof BoolType);
	}

	@Override
	public String toString() {
		return TYPE_NAME;
	}

}
