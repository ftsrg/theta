package hu.bme.mit.inf.theta.core.expr.impl;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.NotExpr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.impl.Types;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;

final class NotExprImpl extends AbstractUnaryExpr<BoolType, BoolType> implements NotExpr {

	private static final int HASH_SEED = 127;

	private static final String OPERAND_LABEL = "Not";

	NotExprImpl(final Expr<? extends BoolType> op) {
		super(op);
	}

	@Override
	public BoolType getType() {
		return Types.Bool();
	}

	@Override
	public NotExpr withOp(final Expr<? extends BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return Exprs.Not(op);
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
		} else if (obj instanceof NotExpr) {
			final NotExpr that = (NotExpr) obj;
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
		return OPERAND_LABEL;
	}

}
