package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.UnaryExpr;

public abstract class NegExpr<ExprType extends Type> extends UnaryExpr<ExprType, ExprType> {

	public NegExpr(final Expr<ExprType> op) {
		super(op);
	}

}
