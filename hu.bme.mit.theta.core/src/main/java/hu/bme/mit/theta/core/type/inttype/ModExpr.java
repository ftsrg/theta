package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.BinaryExpr;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Valuation;

public final class ModExpr extends BinaryExpr<IntType, IntType> {

	private static final int HASH_SEED = 109;
	private static final String OPERATOR_LABEL = "Mod";

	ModExpr(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Valuation val) {
		final IntLitExpr leftOpVal = (IntLitExpr) getLeftOp().eval(val);
		final IntLitExpr rightOpVal = (IntLitExpr) getRightOp().eval(val);
		return leftOpVal.mod(rightOpVal);
	}

	@Override
	public ModExpr with(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new ModExpr(leftOp, rightOp);
		}
	}

	@Override
	public ModExpr withLeftOp(final Expr<IntType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public ModExpr withRightOp(final Expr<IntType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ModExpr) {
			final ModExpr that = (ModExpr) obj;
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