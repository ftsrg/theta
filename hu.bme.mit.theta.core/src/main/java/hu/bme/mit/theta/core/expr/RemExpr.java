package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.IntType;

public interface RemExpr extends BinaryExpr<IntType, IntType, IntType> {

	@Override
	RemExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	@Override
	RemExpr withLeftOp(final Expr<? extends IntType> leftOp);

	@Override
	RemExpr withRightOp(final Expr<? extends IntType> rightOp);
}
