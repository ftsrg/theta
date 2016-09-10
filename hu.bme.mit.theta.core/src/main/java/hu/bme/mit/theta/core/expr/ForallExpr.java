package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public interface ForallExpr extends QuantifiedExpr {
	
	@Override
	public ForallExpr withOp(Expr<? extends BoolType> op);
	
}
