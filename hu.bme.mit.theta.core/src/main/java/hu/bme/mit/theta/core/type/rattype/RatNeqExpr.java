package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.Types.Bool;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class RatNeqExpr extends NeqExpr<RatType> {

	private static final int HASH_SEED = 1997;
	private static final String OPERATOR_LABEL = "Neq";

	RatNeqExpr(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public RatNeqExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new RatNeqExpr(leftOp, rightOp);
		}
	}

	@Override
	public RatNeqExpr withLeftOp(final Expr<? extends RatType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public RatNeqExpr withRightOp(final Expr<? extends RatType> rightOp) {
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
		} else if (obj instanceof RatNeqExpr) {
			final RatNeqExpr that = (RatNeqExpr) obj;
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
