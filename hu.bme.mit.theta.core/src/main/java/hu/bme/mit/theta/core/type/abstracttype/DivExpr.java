package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.BinaryExpr;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;

public abstract class DivExpr<ExprType extends Type> extends BinaryExpr<ExprType, ExprType> {

	protected DivExpr(final Expr<ExprType> leftOp, final Expr<ExprType> rightOp) {
		super(leftOp, rightOp);
	}

}
