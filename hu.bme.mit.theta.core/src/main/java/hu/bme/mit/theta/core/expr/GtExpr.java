package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.RatType;

public interface GtExpr extends BinaryExpr<RatType, RatType, BoolType> {

	@Override
	GtExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	@Override
	GtExpr withLeftOp(final Expr<? extends RatType> leftOp);

	@Override
	GtExpr withRightOp(final Expr<? extends RatType> rightOp);
}
