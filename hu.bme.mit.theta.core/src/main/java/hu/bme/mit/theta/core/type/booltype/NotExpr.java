package hu.bme.mit.theta.core.type.booltype;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Types;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public final class NotExpr extends UnaryExpr<BoolType, BoolType> {

	private static final int HASH_SEED = 127;

	private static final String OPERAND_LABEL = "Not";

	NotExpr(final Expr<? extends BoolType> op) {
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
			return new NotExpr(op);
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
