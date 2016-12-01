package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;

public interface ImplyExpr extends BinaryExpr<BoolType, BoolType, BoolType> {

	@Override
	ImplyExpr withOps(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp);

	@Override
	ImplyExpr withLeftOp(final Expr<? extends BoolType> leftOp);

	@Override
	ImplyExpr withRightOp(final Expr<? extends BoolType> rightOp);
}
