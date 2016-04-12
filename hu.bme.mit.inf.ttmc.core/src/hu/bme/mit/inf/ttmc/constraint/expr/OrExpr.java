package hu.bme.mit.inf.ttmc.constraint.expr;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface OrExpr extends MultiaryExpr<BoolType, BoolType> {
	@Override
	public OrExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
}
