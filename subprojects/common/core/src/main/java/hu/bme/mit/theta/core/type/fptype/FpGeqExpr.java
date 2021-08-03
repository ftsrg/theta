package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.utils.TypeUtils.castFp;
import static hu.bme.mit.theta.core.utils.TypeUtils.checkAllTypesEqual;

public final class FpGeqExpr extends GeqExpr<FpType> {

	private static final int HASH_SEED = 1647;
	private static final String OPERATOR_LABEL = ">=";

	private FpGeqExpr(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		super(leftOp, rightOp);
		checkAllTypesEqual(leftOp, rightOp);
	}

	public static FpGeqExpr of(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		return new FpGeqExpr(leftOp, rightOp);
	}

	public static FpGeqExpr create(final Expr<?> leftOp, final Expr<?> rightOp) {
		final Expr<FpType> newLeftOp = castFp(leftOp);
		final Expr<FpType> newRightOp = castFp(rightOp);
		return FpGeqExpr.of(newLeftOp, newRightOp);
	}

	@Override
	public BoolType getType() {
		return Bool();
	}

	@Override
	public BoolLitExpr eval(final Valuation val) {
		final FpLitExpr leftOpVal = (FpLitExpr) getLeftOp().eval(val);
		final FpLitExpr rightOpVal = (FpLitExpr) getRightOp().eval(val);

		return leftOpVal.geq(rightOpVal);
	}

	@Override
	public FpGeqExpr with(final Expr<FpType> leftOp, final Expr<FpType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return FpGeqExpr.of(leftOp, rightOp);
		}
	}

	@Override
	public FpGeqExpr withLeftOp(final Expr<FpType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public FpGeqExpr withRightOp(final Expr<FpType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof FpGeqExpr) {
			final FpGeqExpr that = (FpGeqExpr) obj;
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
	public String getOperatorLabel() {
		return OPERATOR_LABEL;
	}
}
