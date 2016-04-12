package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface ExistsExpr extends QuantifiedExpr {
	
	@Override
	public ExistsExpr withOp(Expr<? extends BoolType> op);
}
