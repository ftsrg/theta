package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;

public abstract class MulExpr<ExprType extends ClosedUnderMul> extends MultiaryExpr<ExprType, ExprType> {

	protected MulExpr(final Iterable<? extends Expr<ExprType>> ops) {
		super(ops);
	}

}
