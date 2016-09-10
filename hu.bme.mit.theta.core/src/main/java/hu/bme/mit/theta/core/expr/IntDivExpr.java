package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.IntType;

public interface IntDivExpr extends BinaryExpr<IntType, IntType, IntType> {
	
	@Override
	public IntDivExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	@Override
	public IntDivExpr withLeftOp(final Expr<? extends IntType> leftOp);

	@Override
	public IntDivExpr withRightOp(final Expr<? extends IntType> rightOp);
}