package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

public abstract class SubExpr<ExprType extends Type> extends BinaryExpr<ExprType, ExprType> {

	protected SubExpr(final Expr<ExprType> leftOp, final Expr<ExprType> rightOp) {
		super(leftOp, rightOp);
	}

}
