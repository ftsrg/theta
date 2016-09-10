package hu.bme.mit.theta.formalism.common.expr.impl;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.impl.AbstractUnaryExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.ExprVisitor;
import hu.bme.mit.theta.formalism.common.expr.DerefExpr;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public class DerefExprImpl<PointedType extends Type>
		extends AbstractUnaryExpr<PointerType<? extends PointedType>, PointedType> implements DerefExpr<PointedType> {

	private static final int HASH_SEED = 9833;
	private static final String EXPR_LABEL = "Deref";

	public DerefExprImpl(final Expr<? extends PointerType<? extends PointedType>> op) {
		super(op);
	}

	@Override
	public DerefExpr<PointedType> withOp(final Expr<? extends PointerType<? extends PointedType>> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new DerefExprImpl<>(op);
		}
	}

	@Override
	public PointedType getType() {
		return getOp().getType().getPointedType();
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
