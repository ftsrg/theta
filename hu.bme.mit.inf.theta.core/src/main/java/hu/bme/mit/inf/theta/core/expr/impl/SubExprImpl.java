package hu.bme.mit.inf.theta.core.expr.impl;

import java.util.Optional;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.expr.SubExpr;
import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.theta.core.utils.ExprVisitor;
import hu.bme.mit.inf.theta.core.utils.impl.TypeUtils;

final class SubExprImpl<ExprType extends ClosedUnderSub> extends AbstractBinaryExpr<ExprType, ExprType, ExprType>
		implements SubExpr<ExprType> {

	private static final int HASH_SEED = 101;

	private static final String OPERATOR = "Sub";

	SubExprImpl(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public ExprType getType() {
		final ExprType leftType = getLeftOp().getType();
		final ExprType rightType = getRightOp().getType();
		final Optional<ExprType> joinResult = TypeUtils.join(leftType, rightType);
		final ExprType result = joinResult.get();
		return result;
	}

	@Override
	public SubExpr<ExprType> withOps(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return Exprs.Sub(leftOp, rightOp);
		}
	}

	@Override
	public SubExpr<ExprType> withLeftOp(final Expr<? extends ExprType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public SubExpr<ExprType> withRightOp(final Expr<? extends ExprType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

	@Override
	public <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof SubExpr<?>) {
			final SubExpr<?> that = (SubExpr<?>) obj;
			return this.getLeftOp().equals(that.getLeftOp()) && this.getRightOp().equals(that.getRightOp());
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
		return OPERATOR;
	}

}
