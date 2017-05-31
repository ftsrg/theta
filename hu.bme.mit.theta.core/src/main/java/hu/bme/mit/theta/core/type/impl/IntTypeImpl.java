package hu.bme.mit.theta.core.type.impl;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import java.util.Optional;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;

final class IntTypeImpl implements IntType {

	private static final int HASH_SEED = 222670;

	private static final String TYPE_LABEL = "Int";

	IntTypeImpl() {
	}

	@Override
	public LitExpr<IntType> getAny() {
		return Int(0);
	}

	@Override
	public boolean isLeq(final Type type) {
		return type instanceof IntTypeImpl || type instanceof RatTypeImpl;
	}

	@Override
	public Optional<? extends IntType> meet(final Type type) {
		if (type.isLeq(this)) {
			assert type instanceof IntType;
			final IntType that = (IntType) type;
			return Optional.of(that);
		} else if (this.isLeq(type)) {
			return Optional.of(this);
		} else {
			return Optional.empty();
		}
	}

	@Override
	public Optional<? extends RatType> join(final Type type) {
		if (type.isLeq(this)) {
			return Optional.of(this);
		} else if (this.isLeq(type)) {
			assert type instanceof RatType;
			final RatType that = (RatType) type;
			return Optional.of(that);
		} else {
			return Optional.empty();
		}
	}

	@Override
	public int hashCode() {
		return HASH_SEED;
	}

	@Override
	public boolean equals(final Object obj) {
		return (obj instanceof IntTypeImpl);
	}

	@Override
	public String toString() {
		return TYPE_LABEL;
	}
}
