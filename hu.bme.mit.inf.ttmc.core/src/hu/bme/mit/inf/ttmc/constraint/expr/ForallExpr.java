package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface ForallExpr extends QuantifiedExpr {
	
	@Override
	public ForallExpr withOp(Expr<? extends BoolType> op);
	
}
