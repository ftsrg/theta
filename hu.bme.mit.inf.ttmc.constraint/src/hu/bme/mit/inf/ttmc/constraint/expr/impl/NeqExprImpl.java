package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractNeqExpr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public final class NeqExprImpl extends AbstractNeqExpr {

	public NeqExprImpl(Expr<? extends Type> leftOp, Expr<? extends Type> rightOp) {
		super(leftOp, rightOp);
	}

}
