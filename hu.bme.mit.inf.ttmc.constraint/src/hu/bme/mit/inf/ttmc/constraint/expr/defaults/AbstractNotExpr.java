package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.NotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractNotExpr extends AbstractUnaryExpr<BoolType, BoolType> implements NotExpr {

	private static final int HASH_SEED = 127;

	private static final String OPERAND_LABEL = "Not";

	private final ConstraintManager manager;

	public AbstractNotExpr(final ConstraintManager manager, final Expr<? extends BoolType> op) {
		super(op);
		this.manager = manager;
	}

	@Override
	public final BoolType getType() {
		return manager.getTypeFactory().Bool();
	}

	@Override
	public final NotExpr withOp(final Expr<? extends BoolType> op) {
		if (op == getOp()) {
			return this;
		} else {
			return manager.getExprFactory().Not(op);
		}
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final boolean equals(final Object obj) {
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
	protected final int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected final String getOperatorLabel() {
		return OPERAND_LABEL;
	}

}
