package hu.bme.mit.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;

public interface AddExpr<ExprType extends ClosedUnderAdd> extends MultiaryExpr<ExprType, ExprType> {

	@Override
	AddExpr<ExprType> withOps(final Collection<? extends Expr<? extends ExprType>> ops);

}
