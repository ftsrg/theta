package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.BoolType;

public interface ForallExpr extends QuantifiedExpr {
	
	@Override
	public ForallExpr withOp(Expr<? extends BoolType> op);
	
}
