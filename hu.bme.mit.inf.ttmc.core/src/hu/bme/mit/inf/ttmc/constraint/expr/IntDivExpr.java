package hu.bme.mit.inf.ttmc.constraint.expr;

import hu.bme.mit.inf.ttmc.constraint.type.IntType;

public interface IntDivExpr extends BinaryExpr<IntType, IntType, IntType> {
	
	@Override
	public IntDivExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	@Override
	public IntDivExpr withLeftOp(final Expr<? extends IntType> leftOp);

	@Override
	public IntDivExpr withRightOp(final Expr<? extends IntType> rightOp);
}