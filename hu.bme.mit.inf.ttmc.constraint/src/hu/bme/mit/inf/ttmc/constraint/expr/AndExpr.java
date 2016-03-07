package hu.bme.mit.inf.ttmc.constraint.expr;


import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface AndExpr extends MultiaryExpr<BoolType, BoolType> {
	
	@Override
	public AndExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
	
}
