package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.IntType;

public interface ModExpr extends BinaryExpr<IntType, IntType, IntType> {

	@Override
	ModExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	@Override
	ModExpr withLeftOp(final Expr<? extends IntType> leftOp);

	@Override
	ModExpr withRightOp(final Expr<? extends IntType> rightOp);
}