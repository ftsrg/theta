package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface ExistsExpr extends QuantifiedExpr {
	
	@Override
	public ExistsExpr withOp(Expr<? extends BoolType> op);
}
