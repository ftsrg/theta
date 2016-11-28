package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public interface IffExpr extends BinaryExpr<BoolType, BoolType, BoolType> {

	@Override
	IffExpr withOps(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp);

	@Override
	IffExpr withLeftOp(final Expr<? extends BoolType> leftOp);

	@Override
	IffExpr withRightOp(final Expr<? extends BoolType> rightOp);
}
