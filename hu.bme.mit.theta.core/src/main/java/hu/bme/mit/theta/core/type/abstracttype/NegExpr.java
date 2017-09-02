package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.UnaryExpr;

public abstract class NegExpr<ExprType extends Additive<ExprType>> extends UnaryExpr<ExprType, ExprType> {

	public NegExpr(final Expr<ExprType> op) {
		super(op);
	}

}
