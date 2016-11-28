package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;

public interface NegExpr<ExprType extends ClosedUnderNeg> extends UnaryExpr<ExprType, ExprType> {

	@Override
	NegExpr<ExprType> withOp(final Expr<? extends ExprType> op);
}
