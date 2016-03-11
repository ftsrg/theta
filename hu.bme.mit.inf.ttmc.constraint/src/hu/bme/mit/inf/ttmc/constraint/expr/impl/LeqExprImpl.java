package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractLeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class LeqExprImpl extends AbstractLeqExpr {

	public LeqExprImpl(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

}