package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.SubExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;

public class SubExprImpl<ExprType extends ClosedUnderSub> extends AbstractBinaryExpr<ExprType, ExprType, ExprType>
		implements SubExpr<ExprType> {

	private static final String OPERATOR = "Sub";

	public SubExprImpl(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp) {
		super(leftOp, rightOp);
	}

	@Override
	public SubExpr<ExprType> withOps(Expr<? extends ExprType> leftOp, Expr<? extends ExprType> rightOp) {
		if (leftOp == getLeftOp() && rightOp == getRightOp()) {
			return this;
		} else {
			return new SubExprImpl<>(leftOp, rightOp);
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
