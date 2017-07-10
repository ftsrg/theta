package hu.bme.mit.theta.core.type.rattype;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

public final class RatNeqExpr extends NeqExpr<RatType> {

	private static final int HASH_SEED = 1997;
	private static final String OPERATOR_LABEL = "Neq";

	RatNeqExpr(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
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
		return leftOpVal.neq(rightOpVal);
	}

	@Override
	public RatNeqExpr with(final Expr<RatType> leftOp, final Expr<RatType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new RatNeqExpr(leftOp, rightOp);
		}
	}

	@Override
	public RatNeqExpr withLeftOp(final Expr<RatType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public RatNeqExpr withRightOp(final Expr<RatType> rightOp) {
		return with(getLeftOp(), rightOp);
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
