package hu.bme.mit.theta.core.type.inttype;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.impl.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class IntLeqExpr extends LeqExpr<IntType> {

	private static final int HASH_SEED = 4673;
	private static final String OPERATOR_LABEL = "Leq";

	IntLeqExpr(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public IntLeqExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new IntLeqExpr(leftOp, rightOp);
		}
	}

	@Override
	public IntLeqExpr withLeftOp(final Expr<? extends IntType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public IntLeqExpr withRightOp(final Expr<? extends IntType> rightOp) {
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
		} else if (obj instanceof IntLeqExpr) {
			final IntLeqExpr that = (IntLeqExpr) obj;
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