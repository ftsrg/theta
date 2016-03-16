package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractLtExpr;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public final class LtExprImpl extends AbstractLtExpr {

	public LtExprImpl(final ConstraintManager manager, final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp) {
		super(manager, leftOp, rightOp);
	}

}
