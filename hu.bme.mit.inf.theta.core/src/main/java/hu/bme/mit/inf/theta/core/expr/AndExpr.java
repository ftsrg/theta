package hu.bme.mit.inf.theta.core.expr;


import java.util.Collection;

import hu.bme.mit.inf.theta.core.type.BoolType;

public interface AndExpr extends MultiaryExpr<BoolType, BoolType> {
	
	@Override
	public AndExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
	
}
