package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;

public interface NotExpr extends UnaryExpr<BoolType, BoolType> {
	@Override
	public NotExpr withOp(final Expr<? extends BoolType> op);

}
