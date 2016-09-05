package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.closure.ClosedUnderNeg;

public interface NegExpr<ExprType extends ClosedUnderNeg> extends UnaryExpr<ExprType, ExprType> {

	@Override
	public NegExpr<ExprType> withOp(final Expr<? extends ExprType> op);
}
