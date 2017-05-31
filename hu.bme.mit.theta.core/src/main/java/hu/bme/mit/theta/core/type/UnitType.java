package hu.bme.mit.theta.core.type;

import java.util.Optional;

import hu.bme.mit.theta.core.expr.LitExpr;

public final class UnitType implements Type {
	private static final UnitType INSTANCE = new UnitType();
	private static final int HASH_SEED = 5519;
	private static final String TYPE_LABEL = "Unit";

	private UnitType() {
	}

	public static UnitType getInstance() {
		return INSTANCE;
	}

	@Override
	public final LitExpr<UnitType> getAny() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(final Type type) {
		return this.equals(type);
	}

	@Override
	public Optional<? extends Type> meet(final Type type) {
		if (type instanceof UnitType) {
			return Optional.of(this);
		} else {
			return Optional.empty();
		}
	}

	@Override
	public Optional<? extends Type> join(final Type type) {
		if (type instanceof UnitType) {
			return Optional.of(this);
		} else {
			return Optional.empty();
		}
	}

	@Override
	public final int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof UnitType);
	}

	@Override
	public final String toString() {
		return TYPE_LABEL;
	}

}
