package hu.bme.mit.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;

public interface MulExpr<ExprType extends ClosedUnderMul> extends MultiaryExpr<ExprType, ExprType> {

	@Override
	MulExpr<ExprType> withOps(final Collection<? extends Expr<? extends ExprType>> ops);
}
