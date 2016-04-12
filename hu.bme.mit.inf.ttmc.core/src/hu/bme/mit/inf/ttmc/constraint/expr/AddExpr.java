package hu.bme.mit.inf.ttmc.constraint.expr;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderAdd;

public interface AddExpr<ExprType extends ClosedUnderAdd> extends MultiaryExpr<ExprType, ExprType> {

	@Override
	public AddExpr<ExprType> withOps(final Collection<? extends Expr<? extends ExprType>> ops);

}
