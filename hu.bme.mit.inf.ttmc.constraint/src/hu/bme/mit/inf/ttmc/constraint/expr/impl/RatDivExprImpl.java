package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractRatDivExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class RatDivExprImpl extends AbstractRatDivExpr {

	public RatDivExprImpl(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

}