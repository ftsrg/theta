package hu.bme.mit.theta.core.type.impl;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.IntType;

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
