package hu.bme.mit.theta.core.expr;

import java.util.Collection;

import hu.bme.mit.theta.core.type.BoolType;

public interface AndExpr extends MultiaryExpr<BoolType, BoolType> {

	@Override
	AndExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);

}
