package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.RatType;

public interface GeqExpr extends BinaryExpr<RatType, RatType, BoolType> {

	@Override
	GeqExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	@Override
	GeqExpr withLeftOp(final Expr<? extends RatType> leftOp);

	@Override
	GeqExpr withRightOp(final Expr<? extends RatType> rightOp);

}