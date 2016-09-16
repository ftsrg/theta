package hu.bme.mit.theta.core.expr.impl;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;

final class PrimedExprImpl<ExprType extends Type> extends AbstractUnaryExpr<ExprType, ExprType>
		implements PrimedExpr<ExprType> {

	private static final int HASH_SEED = 4561;

	private static final String OPERATOR_LABEL = "Prime";

	PrimedExprImpl(final Expr<? extends ExprType> op) {
		super(op);
	}

	@Override
	public final ExprType getType() {
		return getOp().getType();
	}

	@Override
	public final UnaryExpr<ExprType, ExprType> withOp(final Expr<? extends ExprType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new PrimedExprImpl<>(op);
		}
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof PrimedExpr) {
			final PrimedExpr<?> that = (PrimedExpr<?>) obj;
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
