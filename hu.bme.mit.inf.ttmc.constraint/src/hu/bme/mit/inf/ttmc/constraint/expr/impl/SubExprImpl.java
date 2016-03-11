package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractSubExpr;
import hu.bme.mit.inf.ttmc.constraint.type.closure.ClosedUnderSub;

public final class SubExprImpl<ExprType extends ClosedUnderSub> extends AbstractSubExpr<ExprType> {

	public SubExprImpl(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp) {
		super(leftOp, rightOp);
	}

}
