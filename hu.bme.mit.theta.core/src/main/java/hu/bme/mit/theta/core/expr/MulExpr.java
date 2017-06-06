package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

public abstract class MulExpr<ExprType extends Type> extends MultiaryExpr<ExprType, ExprType> {

	protected MulExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
