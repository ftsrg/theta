package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.MultiaryExpr;
import hu.bme.mit.theta.core.Type;

public abstract class AddExpr<ExprType extends Type> extends MultiaryExpr<ExprType, ExprType> {

	public AddExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
