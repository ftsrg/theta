package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.BoolType;

public interface NotExpr extends UnaryExpr<BoolType, BoolType> {
	@Override
	public NotExpr withOp(final Expr<? extends BoolType> op);

}
