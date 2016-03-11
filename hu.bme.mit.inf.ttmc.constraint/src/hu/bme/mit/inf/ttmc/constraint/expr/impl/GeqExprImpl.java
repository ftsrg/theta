package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractGeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class GeqExprImpl extends AbstractGeqExpr {

	public GeqExprImpl(Expr<? extends RatType> leftOp, Expr<? extends RatType> rightOp) {
		super(leftOp, rightOp);
	}

}