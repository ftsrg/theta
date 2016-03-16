package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractNotExpr extends AbstractUnaryExpr<BoolType, BoolType> implements NotExpr {

	private static final String OPERAND = "Not";

	public AbstractNotExpr(final Expr<? extends BoolType> op) {
		super(op);
	}

	@Override
	public final NotExpr withOp(final Expr<? extends BoolType> op) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
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
	protected final String getOperatorString() {
		return OPERAND;
	}

	@Override
	protected int getHashSeed() {
		return 127;
	}
}
