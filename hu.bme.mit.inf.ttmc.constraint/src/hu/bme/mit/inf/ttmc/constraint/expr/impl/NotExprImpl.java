package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractNotExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public final class NotExprImpl extends AbstractNotExpr {

	public NotExprImpl(Expr<? extends BoolType> op) {
		super(op);
	}

}
