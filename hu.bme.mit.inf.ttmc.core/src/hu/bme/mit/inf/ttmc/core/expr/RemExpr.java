package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.IntType;

public interface RemExpr extends BinaryExpr<IntType, IntType, IntType> {

	@Override
	public RemExpr withOps(final Expr<? extends IntType> leftOp, final Expr<? extends IntType> rightOp);

	@Override
	public RemExpr withLeftOp(final Expr<? extends IntType> leftOp);

	@Override
	public RemExpr withRightOp(final Expr<? extends IntType> rightOp);
}
