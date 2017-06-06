package hu.bme.mit.theta.core.type.abstracttype;

import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.MultiaryExpr;
import hu.bme.mit.theta.core.Type;

public abstract class MulExpr<ExprType extends Type> extends MultiaryExpr<ExprType, ExprType> {

	protected MulExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
