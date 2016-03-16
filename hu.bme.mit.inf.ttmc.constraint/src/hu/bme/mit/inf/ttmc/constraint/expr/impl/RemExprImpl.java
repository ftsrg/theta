package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractRemExpr;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public final class RemExprImpl extends AbstractRemExpr {

	public RemExprImpl(final ConstraintManager manager, final Expr<? extends IntType> leftOp,
			final Expr<? extends IntType> rightOp) {
		super(manager, leftOp, rightOp);
	}

}