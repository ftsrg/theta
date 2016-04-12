package hu.bme.mit.inf.ttmc.core.expr;


import java.util.Collection;

import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface AndExpr extends MultiaryExpr<BoolType, BoolType> {
	
	@Override
	public AndExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
	
}
