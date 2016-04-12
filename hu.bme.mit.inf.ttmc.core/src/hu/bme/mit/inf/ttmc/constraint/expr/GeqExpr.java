package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public interface GeqExpr extends BinaryExpr<RatType, RatType, BoolType> {
	
	@Override
	public GeqExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);
	
	@Override
	public GeqExpr withLeftOp(final Expr<? extends RatType> leftOp);

	@Override
	public GeqExpr withRightOp(final Expr<? extends RatType> rightOp);

}