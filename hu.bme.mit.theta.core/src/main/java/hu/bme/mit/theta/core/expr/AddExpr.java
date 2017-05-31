package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;

public abstract class AddExpr<ExprType extends ClosedUnderAdd> extends MultiaryExpr<ExprType, ExprType> {

	public AddExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
