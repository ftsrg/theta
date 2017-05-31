package hu.bme.mit.theta.core.type;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

import hu.bme.mit.theta.core.expr.LitExpr;

public final class BoolType implements Type {
	private static final BoolType INSTANCE = new BoolType();
	private static final int HASH_SEED = 754364;
	private static final String TYPE_LABEL = "Bool";

	private BoolType() {
	}

	public static BoolType getInstance() {
		return INSTANCE;
	}

	@Override
	public LitExpr<BoolType> getAny() {
		return False();
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
