package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;

public abstract class SubExpr<ExprType extends ClosedUnderSub> extends BinaryExpr<ExprType, ExprType> {

	protected SubExpr(final Expr<ExprType> leftOp, final Expr<ExprType> rightOp) {
		super(leftOp, rightOp);
	}

}
