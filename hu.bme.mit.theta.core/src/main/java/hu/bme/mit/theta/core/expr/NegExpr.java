package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

public abstract class NegExpr<ExprType extends Type> extends UnaryExpr<ExprType, ExprType> {

	public NegExpr(final Expr<ExprType> op) {
		super(op);
	}

}
