package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

public interface NeqExpr extends BinaryExpr<Type, Type, BoolType> {

	@Override
	NeqExpr withOps(final Expr<? extends Type> leftOp, final Expr<? extends Type> rightOp);

	@Override
	NeqExpr withLeftOp(final Expr<? extends Type> leftOp);

	@Override
	NeqExpr withRightOp(final Expr<? extends Type> rightOp);
}
