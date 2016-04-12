package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface ForallExpr extends QuantifiedExpr {
	
	@Override
	public ForallExpr withOp(Expr<? extends BoolType> op);
	
}
