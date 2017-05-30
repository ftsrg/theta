package hu.bme.mit.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;

public abstract class MulExpr<ExprType extends ClosedUnderMul> extends MultiaryExpr<ExprType, ExprType> {

	protected MulExpr(final Collection<? extends Expr<? extends ExprType>> ops) {
		super(ops);
	}

}
