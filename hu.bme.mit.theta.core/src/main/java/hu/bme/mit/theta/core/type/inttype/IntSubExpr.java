package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.abstracttype.SubExpr;

public final class IntSubExpr extends SubExpr<IntType> {

	private static final int HASH_SEED = 4547;
	private static final String OPERATOR = "Sub";

	IntSubExpr(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Assignment assignment) {
		final IntLitExpr leftOpVal = (IntLitExpr) getLeftOp().eval(assignment);
		final IntLitExpr rightOpVal = (IntLitExpr) getRightOp().eval(assignment);
		return leftOpVal.sub(rightOpVal);
	}

	@Override
	public SubExpr<IntType> with(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new IntSubExpr(leftOp, rightOp);
		}
	}

	@Override
	public SubExpr<IntType> withLeftOp(final Expr<IntType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public SubExpr<IntType> withRightOp(final Expr<IntType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntSubExpr) {
			final IntSubExpr that = (IntSubExpr) obj;
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
