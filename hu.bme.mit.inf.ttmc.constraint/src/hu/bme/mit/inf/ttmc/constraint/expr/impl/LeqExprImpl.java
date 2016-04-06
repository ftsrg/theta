package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractLeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class LeqExprImpl extends AbstractLeqExpr {

	public LeqExprImpl(final ConstraintManager manager, final Expr<? extends RatType> leftOp,
			final Expr<? extends RatType> rightOp) {
		super(manager, leftOp, rightOp);
	}

}