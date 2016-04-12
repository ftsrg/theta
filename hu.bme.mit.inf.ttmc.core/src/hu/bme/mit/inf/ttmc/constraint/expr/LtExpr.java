package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;

public interface LtExpr extends BinaryExpr<RatType, RatType, BoolType> {
	
	@Override
	public LtExpr withOps(final Expr<? extends RatType> leftOp, final Expr<? extends RatType> rightOp);
	
	@Override
	public LtExpr withLeftOp(final Expr<? extends RatType> leftOp);

	@Override
	public LtExpr withRightOp(final Expr<? extends RatType> rightOp);
}

