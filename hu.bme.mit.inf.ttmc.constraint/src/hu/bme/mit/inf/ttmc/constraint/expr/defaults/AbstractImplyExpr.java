package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractImplyExpr extends AbstractBinaryExpr<BoolType, BoolType, BoolType> implements ImplyExpr {

	private static final int HASH_SEED = 71;

	private static final String OPERATOR_LABEL = "Imply";

	private final ConstraintManager manager;

	public AbstractImplyExpr(final ConstraintManager manager, final Expr<? extends BoolType> leftOp,
			final Expr<? extends BoolType> rightOp) {
		super(leftOp, rightOp);
		this.manager = manager;
	}

	@Override
	public final ImplyExpr withOps(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return manager.getExprFactory().Imply(leftOp, rightOp);
		}
	}

	@Override
	public final ImplyExpr withLeftOp(final Expr<? extends BoolType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final ImplyExpr withRightOp(final Expr<? extends BoolType> rightOp) {
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
		} else if (obj instanceof ImplyExpr) {
			final ImplyExpr that = (ImplyExpr) obj;
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
