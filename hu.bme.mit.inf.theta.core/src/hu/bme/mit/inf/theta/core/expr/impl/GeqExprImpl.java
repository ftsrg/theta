package hu.bme.mit.inf.theta.core.expr.impl;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.GeqExpr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.core.type.impl.Types;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;

final class GeqExprImpl extends AbstractBinaryExpr<RatType, RatType, BoolType> implements GeqExpr {

	private static final int HASH_SEED = 59;

	private static final String OPERATOR_LABEL = "Geq";

	GeqExprImpl(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public GeqExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return Exprs.Geq(leftOp, rightOp);
		}
	}

	@Override
	public GeqExpr withLeftOp(final Expr<? extends RatType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public GeqExpr withRightOp(final Expr<? extends RatType> rightOp) {
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
		} else if (obj instanceof GeqExpr) {
			final GeqExpr that = (GeqExpr) obj;
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