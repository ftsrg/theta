package hu.bme.mit.theta.formalism.common.expr;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public class DerefExpr<PointedType extends Type> extends UnaryExpr<PointerType<? extends PointedType>, PointedType> {

	private static final int HASH_SEED = 9833;
	private static final String EXPR_LABEL = "Deref";

	public DerefExpr(final Expr<PointerType<? extends PointedType>> op) {
		super(op);
	}

	@Override
	public DerefExpr<PointedType> with(final Expr<PointerType<? extends PointedType>> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new DerefExpr<>(op);
		}
	}

	@Override
	public PointedType getType() {
		return getOp().getType().getPointedType();
	}

	@Override
	protected int getHashSeed() {
		return HASH_SEED;
	}

	@Override
	protected String getOperatorLabel() {
		return EXPR_LABEL;
	}

}
