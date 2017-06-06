package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

public abstract class AddExpr<ExprType extends Type> extends MultiaryExpr<ExprType, ExprType> {

	public AddExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
