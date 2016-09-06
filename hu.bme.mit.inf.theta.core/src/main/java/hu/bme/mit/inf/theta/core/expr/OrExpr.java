package hu.bme.mit.inf.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.inf.theta.core.type.BoolType;

public interface OrExpr extends MultiaryExpr<BoolType, BoolType> {
	@Override
	public OrExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
}
