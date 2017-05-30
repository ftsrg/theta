package hu.bme.mit.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;

public abstract class AddExpr<ExprType extends ClosedUnderAdd> extends MultiaryExpr<ExprType, ExprType> {

	public AddExpr(final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ops);
	}

}
