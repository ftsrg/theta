package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.abstracttype.MulExpr;

public final class RatMulExpr extends MulExpr<RatType> {

	private static final int HASH_SEED = 9479;
	private static final String OPERATOR_LABEL = "Mul";

	RatMulExpr(final Iterable<? extends Expr<RatType>> ops) {
		super(ops);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public RatMulExpr with(final Iterable<? extends Expr<RatType>> ops) {
		if (ops == getOps()) {
			return this;
		} else {
			return new RatMulExpr(ops);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatMulExpr) {
			final RatMulExpr that = (RatMulExpr) obj;
			return this.getOps().equals(that.getOps());
		} else {
			return false;
		}
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
