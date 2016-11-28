package hu.bme.mit.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.theta.core.type.BoolType;

public interface OrExpr extends MultiaryExpr<BoolType, BoolType> {
	@Override
	OrExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
}
