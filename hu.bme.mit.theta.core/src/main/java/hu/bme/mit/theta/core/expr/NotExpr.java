package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public interface NotExpr extends UnaryExpr<BoolType, BoolType> {
	@Override
	public NotExpr withOp(final Expr<? extends BoolType> op);

}
