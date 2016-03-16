package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractGeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class GeqExprImpl extends AbstractGeqExpr {

	public GeqExprImpl(final ConstraintManager manager, final Expr<? extends RatType> leftOp,
			final Expr<? extends RatType> rightOp) {
		super(manager, leftOp, rightOp);
	}

}