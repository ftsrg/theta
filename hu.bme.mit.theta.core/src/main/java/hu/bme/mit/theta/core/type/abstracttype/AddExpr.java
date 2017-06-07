package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.MultiaryExpr;

public abstract class AddExpr<ExprType extends Additive<ExprType>> extends MultiaryExpr<ExprType, ExprType> {

	public AddExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
