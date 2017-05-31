package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.Types.Rat;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class RatNegExpr extends NegExpr<RatType> {

	private static final int HASH_SEED = 4127;
	private static final String OPERATOR_LABEL = "Neg";

	RatNegExpr(final Expr<? extends RatType> op) {
		super(op);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public RatNegExpr withOp(final Expr<? extends RatType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new RatNegExpr(op);
		}
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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
