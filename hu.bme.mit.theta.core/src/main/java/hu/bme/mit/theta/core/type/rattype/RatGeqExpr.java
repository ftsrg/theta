package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Assignment;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class RatGeqExpr extends GeqExpr<RatType> {

	private static final int HASH_SEED = 6101;
	private static final String OPERATOR_LABEL = "Geq";

	RatGeqExpr(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Assignment assignment) {
		final RatLitExpr leftOpVal = (RatLitExpr) getLeftOp().eval(assignment);
		final RatLitExpr rightOpVal = (RatLitExpr) getRightOp().eval(assignment);
		return leftOpVal.geq(rightOpVal);
	}

	@Override
	public RatGeqExpr with(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new RatGeqExpr(leftOp, rightOp);
		}
	}

	@Override
	public RatGeqExpr withLeftOp(final Expr<RatType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public RatGeqExpr withRightOp(final Expr<RatType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatGeqExpr) {
			final RatGeqExpr that = (RatGeqExpr) obj;
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