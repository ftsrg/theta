package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public interface ExistsExpr extends QuantifiedExpr {

	@Override
	ExistsExpr withOp(Expr<? extends BoolType> op);
}
