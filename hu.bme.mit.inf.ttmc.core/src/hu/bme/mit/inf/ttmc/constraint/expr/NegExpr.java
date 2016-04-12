package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderNeg;

public interface NegExpr<ExprType extends ClosedUnderNeg> extends UnaryExpr<ExprType, ExprType> {

	@Override
	public NegExpr<ExprType> withOp(final Expr<? extends ExprType> op);
}
