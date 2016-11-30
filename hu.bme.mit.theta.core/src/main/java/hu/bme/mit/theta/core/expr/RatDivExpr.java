package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.RatType;

public interface RatDivExpr extends BinaryExpr<RatType, RatType, RatType> {

	@Override
	RatDivExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	@Override
	RatDivExpr withLeftOp(final Expr<? extends RatType> leftOp);

	@Override
	RatDivExpr withRightOp(final Expr<? extends RatType> rightOp);
}