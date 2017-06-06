package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.Type;

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
	public LitExpr<IntType> getAny() {
		return Int(0);
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
