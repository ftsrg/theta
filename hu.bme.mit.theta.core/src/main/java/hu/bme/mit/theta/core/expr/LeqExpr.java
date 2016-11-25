package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.RatType;

public interface LeqExpr extends BinaryExpr<RatType, RatType, BoolType> {

	@Override
	LeqExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	@Override
	LeqExpr withLeftOp(final Expr<? extends RatType> leftOp);

	@Override
	LeqExpr withRightOp(final Expr<? extends RatType> rightOp);
}