package hu.bme.mit.theta.core.type.inttype;

import static hu.bme.mit.theta.core.type.Types.Int;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class IntNegExpr extends NegExpr<IntType> {

	private static final int HASH_SEED = 3359;
	private static final String OPERATOR_LABEL = "Neg";

	IntNegExpr(final Expr<? extends IntType> op) {
		super(op);
	}

	@Override
	public IntType getType() {
		return Int();
	}

	@Override
	public IntNegExpr withOp(final Expr<? extends IntType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new IntNegExpr(op);
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
