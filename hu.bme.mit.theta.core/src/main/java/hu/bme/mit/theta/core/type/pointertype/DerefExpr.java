package hu.bme.mit.theta.core.type.pointertype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.UnaryExpr;
import hu.bme.mit.theta.core.model.Substitution;

public class DerefExpr<PointedType extends Type> extends UnaryExpr<PointerType<PointedType>, PointedType> {

	private static final int HASH_SEED = 9833;
	private static final String EXPR_LABEL = "Deref";

	public DerefExpr(final Expr<PointerType<PointedType>> op) {
		super(op);
	}

	@Override
	public PointedType getType() {
		return getOp().getType().getPointedType();
	}

	@Override
	public LitExpr<PointedType> eval(final Substitution assignment) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public DerefExpr<PointedType> with(final Expr<PointerType<PointedType>> op) {
		if (op == getOp()) {
			return this;
		} else {
			return new DerefExpr<>(op);
		}
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
