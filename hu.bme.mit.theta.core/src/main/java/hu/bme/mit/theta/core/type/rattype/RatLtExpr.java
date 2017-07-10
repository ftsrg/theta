package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.abstracttype.LtExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class RatLtExpr extends LtExpr<RatType> {

	private static final int HASH_SEED = 6311;
	private static final String OPERATOR_LABEL = "Lt";

	RatLtExpr(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		final RatLitExpr leftOpVal = (RatLitExpr) getLeftOp().eval(val);
		final RatLitExpr rightOpVal = (RatLitExpr) getRightOp().eval(val);
		return leftOpVal.lt(rightOpVal);
	}

	@Override
	public RatLtExpr with(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new RatLtExpr(leftOp, rightOp);
		}
	}

	@Override
	public RatLtExpr withLeftOp(final Expr<RatType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public RatLtExpr withRightOp(final Expr<RatType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RatLtExpr) {
			final RatLtExpr that = (RatLtExpr) obj;
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
