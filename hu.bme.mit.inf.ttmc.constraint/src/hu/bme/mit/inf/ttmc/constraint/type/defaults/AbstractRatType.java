package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public abstract class AbstractRatType extends AbstractBaseType implements RatType {

	private static final int HASH_SEED = 385863;

	private static final String TYPE_NAME = "Rat";

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof RatType);
	}

	@Override
	public String toString() {
		return TYPE_NAME;
	}

}
