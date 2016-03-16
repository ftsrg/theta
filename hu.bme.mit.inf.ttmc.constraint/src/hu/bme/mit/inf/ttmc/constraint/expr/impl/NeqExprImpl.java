package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractNeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class NeqExprImpl extends AbstractNeqExpr {

	public NeqExprImpl(final ConstraintManager manager, final Expr<? extends Type> leftOp,
			final Expr<? extends Type> rightOp) {
		super(manager, leftOp, rightOp);
	}

}
