package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;

public abstract class NegExpr<ExprType extends ClosedUnderNeg> extends UnaryExpr<ExprType, ExprType> {

	public NegExpr(final Expr<? extends ExprType> op) {
		super(op);
		// TODO Auto-generated constructor stub
	}

}
