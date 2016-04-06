package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractIntLitExpr;

public final class IntLitExprImpl extends AbstractIntLitExpr {

	public IntLitExprImpl(final ConstraintManager manager, final long value) {
		super(manager, value);
	}

}
