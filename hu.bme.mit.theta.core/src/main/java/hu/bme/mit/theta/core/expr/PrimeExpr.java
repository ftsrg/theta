package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

public final class PrimeExpr<ExprType extends Type> extends UnaryExpr<ExprType, ExprType> {

	private static final int HASH_SEED = 4561;

	private static final String OPERATOR_LABEL = "Prime";

	PrimeExpr(final Expr<ExprType> op) {
		super(op);
	}

	@Override
	public final ExprType getType() {
		return getOp().getType();
	}

	@Override
	public final UnaryExpr<ExprType, ExprType> with(final Expr<ExprType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new PrimeExpr<>(op);
		}
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof PrimeExpr) {
			final PrimeExpr<?> that = (PrimeExpr<?>) obj;
			return this.getOp().equals(that.getOp());
		} else {
			return false;
		}
	}

	@Override
	protected final int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected final String getOperatorLabel() {
		return OPERATOR_LABEL;
	}

}
