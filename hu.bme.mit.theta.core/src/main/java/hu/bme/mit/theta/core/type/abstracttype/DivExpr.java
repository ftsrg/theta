package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.BinaryExpr;
import hu.bme.mit.theta.core.type.Expr;

public abstract class DivExpr<ExprType extends Multiplicative<ExprType>> extends BinaryExpr<ExprType, ExprType> {

	protected DivExpr(final Expr<ExprType> leftOp, final Expr<ExprType> rightOp) {
		super(leftOp, rightOp);
	}

}
