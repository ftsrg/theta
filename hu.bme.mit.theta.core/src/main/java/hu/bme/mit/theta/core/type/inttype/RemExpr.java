package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.BinaryExpr;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.model.Assignment;

public final class RemExpr extends BinaryExpr<IntType, IntType> {

	private static final int HASH_SEED = 199;

	private static final String OPERATOR_LABEL = "Rem";

	RemExpr(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntLitExpr eval(final Assignment assignment) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public RemExpr with(final Expr<IntType> leftOp, final Expr<IntType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new RemExpr(leftOp, rightOp);
		}
	}

	@Override
	public RemExpr withLeftOp(final Expr<IntType> leftOp) {
		return with(leftOp, getRightOp());
	}

	@Override
	public RemExpr withRightOp(final Expr<IntType> rightOp) {
		return with(getLeftOp(), rightOp);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof RemExpr) {
			final RemExpr that = (RemExpr) obj;
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