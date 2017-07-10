package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class IntLtExpr extends LtExpr<IntType> {

	private static final int HASH_SEED = 9431;
	private static final String OPERATOR_LABEL = "Lt";

	IntLtExpr(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public LitExpr<BoolType> eval(final Valuation val) {
		final IntLitExpr leftOpVal = (IntLitExpr) getLeftOp().eval(val);
		final IntLitExpr rightOpVal = (IntLitExpr) getRightOp().eval(val);
		return leftOpVal.lt(rightOpVal);
	}

	@Override
	public IntLtExpr with(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new IntLtExpr(leftOp, rightOp);
		}
	}

	@Override
	public IntLtExpr withLeftOp(final Expr<IntType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public IntLtExpr withRightOp(final Expr<IntType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntLtExpr) {
			final IntLtExpr that = (IntLtExpr) obj;
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
