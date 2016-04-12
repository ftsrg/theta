package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;

public interface NegExpr<ExprType extends ClosedUnderNeg> extends UnaryExpr<ExprType, ExprType> {

	@Override
	public NegExpr<ExprType> withOp(final Expr<? extends ExprType> op);
}
