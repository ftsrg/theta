package hu.bme.mit.inf.ttmc.core.expr;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface OrExpr extends MultiaryExpr<BoolType, BoolType> {
	@Override
	public OrExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
}
