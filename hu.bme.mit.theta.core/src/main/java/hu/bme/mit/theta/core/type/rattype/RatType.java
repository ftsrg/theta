package hu.bme.mit.theta.core.type.rattype;

import hu.bme.mit.theta.core.Type;

public final class RatType implements Type {
	private static final RatType INSTANCE = new RatType();
	private static final int HASH_SEED = 385863;
	private static final String TYPE_LABEL = "Rat";

	private RatType() {
	}

	static RatType getInstance() {
		return INSTANCE;
	}

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
		return TYPE_LABEL;
	}

}
