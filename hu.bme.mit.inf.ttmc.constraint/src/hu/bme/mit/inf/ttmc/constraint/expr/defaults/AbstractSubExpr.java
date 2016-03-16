package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractSubExpr<ExprType extends ClosedUnderSub>
		extends AbstractBinaryExpr<ExprType, ExprType, ExprType> implements SubExpr<ExprType> {

	private static final String OPERATOR = "Sub";

	public AbstractSubExpr(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public SubExpr<ExprType> withOps(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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
	protected final String getOperatorString() {
		return OPERATOR;
	}

	@Override
	protected final int getHashSeed() {
		return 101;
	}
}
