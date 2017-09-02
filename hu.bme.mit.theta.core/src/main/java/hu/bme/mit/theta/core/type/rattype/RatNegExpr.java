package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;

public final class RatNegExpr extends NegExpr<RatType> {

	private static final int HASH_SEED = 4127;
	private static final String OPERATOR_LABEL = "Neg";

	RatNegExpr(final Expr<RatType> op) {
		super(op);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public RatLitExpr eval(final Valuation val) {
		final RatLitExpr opVal = (RatLitExpr) getOp().eval(val);
		return opVal.neg();
	}

	@Override
	public RatNegExpr with(final Expr<RatType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new RatNegExpr(op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatNegExpr) {
			final RatNegExpr that = (RatNegExpr) obj;
			return this.getOp().equals(that.getOp());
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
