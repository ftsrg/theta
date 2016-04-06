package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractGtExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class GtExprImpl extends AbstractGtExpr {

	public GtExprImpl(final ConstraintManager manager, final Expr<? extends RatType> leftOp,
			final Expr<? extends RatType> rightOp) {
		super(manager, leftOp, rightOp);
	}
}
