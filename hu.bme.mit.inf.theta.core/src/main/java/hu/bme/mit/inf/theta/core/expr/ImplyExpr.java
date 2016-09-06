package hu.bme.mit.inf.theta.core.expr;

import hu.bme.mit.inf.theta.core.type.BoolType;

public interface ImplyExpr extends BinaryExpr<BoolType, BoolType, BoolType> {
	
	@Override
	public ImplyExpr withOps(final Expr<? extends BoolType> leftOp, final Expr<? extends BoolType> rightOp);
	
	@Override
	public ImplyExpr withLeftOp(final Expr<? extends BoolType> leftOp);

	@Override
	public ImplyExpr withRightOp(final Expr<? extends BoolType> rightOp);
}
