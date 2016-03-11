package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractOrExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public final class OrExprImpl extends AbstractOrExpr {

	public OrExprImpl(final Collection<? extends Expr<? extends BoolType>> ops) {
		super(ops);
	}

}
