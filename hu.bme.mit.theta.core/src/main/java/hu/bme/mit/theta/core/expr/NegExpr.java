package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class NegExpr<ExprType extends ClosedUnderNeg> extends UnaryExpr<ExprType, ExprType>{

	private static final int HASH_SEED = 97;

	private static final String OPERATOR_LABEL = "Neg";

	NegExpr(final Expr<? extends ExprType> op) {
		super(op);
	}

	@Override
	public ExprType getType() {
		return getOp().getType();
	}

	@Override
	public NegExpr<ExprType> withOp(final Expr<? extends ExprType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return Exprs.Neg(op);
		}
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof NegExpr<?>) {
			final NegExpr<?> that = (NegExpr<?>) obj;
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
