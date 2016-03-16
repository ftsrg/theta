package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractRatLitExpr;

public final class RatLitExprImpl extends AbstractRatLitExpr {

	public RatLitExprImpl(final ConstraintManager manager, final long num, final long denom) {
		super(manager, num, denom);
	}

}
