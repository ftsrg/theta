package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

public abstract class DivExpr<ExprType extends Type> extends BinaryExpr<ExprType, ExprType, ExprType> {

	protected DivExpr(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp) {
		super(leftOp, rightOp);
	}

}
