package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.type.abstracttype.NegExpr;

public final class IntNegExpr extends NegExpr<IntType> {

	private static final int HASH_SEED = 3359;
	private static final String OPERATOR_LABEL = "Neg";

	IntNegExpr(final Expr<IntType> op) {
		super(op);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntNegExpr with(final Expr<IntType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new IntNegExpr(op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof IntNegExpr) {
			final IntNegExpr that = (IntNegExpr) obj;
			return this.getOp().equals(that.getOp());
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
