package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractRatDivExpr extends AbstractBinaryExpr<RatType, RatType, RatType> implements RatDivExpr {

	private static final int HASH_SEED = 139;

	private static final String OPERATOR_LABEL = "RDiv";

	public AbstractRatDivExpr(final ConstraintManager manager, final Expr<? extends RatType> leftOp,
			final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public final RatDivExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final RatDivExpr withLeftOp(final Expr<? extends RatType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public final RatDivExpr withRightOp(final Expr<? extends RatType> rightOp) {
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
		} else if (obj instanceof RatDivExpr) {
			final RatDivExpr that = (RatDivExpr) obj;
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