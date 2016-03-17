package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.EqExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractEqExpr extends AbstractBinaryExpr<Type, Type, BoolType> implements EqExpr {

	private static final int HASH_SEED = 43;

	private static final String OPERATOR_LABEL = "Eq";

	private final ConstraintManager manager;

	public AbstractEqExpr(final ConstraintManager manager, final Expr<? extends Type> leftOp,
			final Expr<? extends Type> rightOp) {
		super(leftOp, rightOp);
		this.manager = manager;
	}

	@Override
	public final BoolType getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final EqExpr withOps(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return manager.getExprFactory().Eq(leftOp, rightOp);
		}
	}

	@Override
	public final EqExpr withLeftOp(final Expr<? extends Type> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final EqExpr withRightOp(final Expr<? extends Type> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof EqExpr) {
			final EqExpr that = (EqExpr) obj;
			return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
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
