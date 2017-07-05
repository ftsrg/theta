package hu.bme.mit.theta.core.type.booltype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.BinaryExpr;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Substitution;

public final class ImplyExpr extends BinaryExpr<BoolType, BoolType> {

	private static final int HASH_SEED = 71;

	private static final String OPERATOR_LABEL = "Imply";

	ImplyExpr(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Substitution assignment) {
		final BoolLitExpr leftOpVal = (BoolLitExpr) getLeftOp().eval(assignment);
		final BoolLitExpr rightOpVal = (BoolLitExpr) getRightOp().eval(assignment);
		return Bool(!leftOpVal.getValue() || rightOpVal.getValue());
	}

	@Override
	public ImplyExpr with(final Expr<BoolType> leftOp, final Expr<BoolType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new ImplyExpr(leftOp, rightOp);
		}
	}

	@Override
	public ImplyExpr withLeftOp(final Expr<BoolType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public ImplyExpr withRightOp(final Expr<BoolType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ImplyExpr) {
			final ImplyExpr that = (ImplyExpr) obj;
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
