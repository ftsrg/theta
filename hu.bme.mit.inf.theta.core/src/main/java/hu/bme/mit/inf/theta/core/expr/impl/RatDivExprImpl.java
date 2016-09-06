package hu.bme.mit.inf.theta.core.expr.impl;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.RatDivExpr;
import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.core.type.impl.Types;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;

final class RatDivExprImpl extends AbstractBinaryExpr<RatType, RatType, RatType> implements RatDivExpr {

	private static final int HASH_SEED = 139;

	private static final String OPERATOR_LABEL = "RDiv";

	RatDivExprImpl(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public RatType getType() {
		return Types.Rat();
	}

	@Override
	public RatDivExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return Exprs.RatDiv(leftOp, rightOp);
		}
	}

	@Override
	public RatDivExpr withLeftOp(final Expr<? extends RatType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public RatDivExpr withRightOp(final Expr<? extends RatType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatDivExpr) {
			final RatDivExpr that = (RatDivExpr) obj;
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
		return OPERATOR_LABEL;
	}

}