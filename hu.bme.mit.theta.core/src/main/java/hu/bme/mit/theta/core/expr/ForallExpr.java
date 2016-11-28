package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public interface ForallExpr extends QuantifiedExpr {

	@Override
	ForallExpr withOp(Expr<? extends BoolType> op);

}
