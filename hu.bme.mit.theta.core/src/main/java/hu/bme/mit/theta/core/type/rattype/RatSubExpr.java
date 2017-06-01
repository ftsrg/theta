package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.rattype.RatExprs.Rat;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class RatSubExpr extends SubExpr<RatType> {

	private static final int HASH_SEED = 6287;
	private static final String OPERATOR = "Sub";

	RatSubExpr(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public RatType getType() {
		return Rat();
	}

	@Override
	public SubExpr<RatType> with(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new RatSubExpr(leftOp, rightOp);
		}
	}

	@Override
	public SubExpr<RatType> withLeftOp(final Expr<RatType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public SubExpr<RatType> withRightOp(final Expr<RatType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatSubExpr) {
			final RatSubExpr that = (RatSubExpr) obj;
			return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
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
		return OPERATOR;
	}

}
