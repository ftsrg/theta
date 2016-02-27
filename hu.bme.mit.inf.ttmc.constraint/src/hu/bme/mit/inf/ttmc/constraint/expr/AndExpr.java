package hu.bme.mit.inf.ttmc.constraint.expr;


import java.util.Collection;

import hu.bme.mit.inf.ttmc.constraint.expr.AndExpr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public interface AndExpr extends MultiaryExpr<BoolType, BoolType> {
	
	@Override
	public AndExpr withOps(final Collection<? extends Expr<? extends BoolType>> ops);
	
	@Override
	public default <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
