package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.Type;

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
	public LitExpr<RatType> getAny() {
		return Rat(0, 1);
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
