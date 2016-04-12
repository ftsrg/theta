package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.RatType;

public interface GtExpr extends BinaryExpr<RatType, RatType, BoolType> {

	@Override
	public GtExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);

	@Override
	public GtExpr withLeftOp(final Expr<? extends RatType> leftOp);

	@Override
	public GtExpr withRightOp(final Expr<? extends RatType> rightOp);
}
