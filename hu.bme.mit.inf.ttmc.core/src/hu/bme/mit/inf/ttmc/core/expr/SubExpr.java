package hu.bme.mit.inf.ttmc.core.expr;

import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;

public interface SubExpr<ExprType extends ClosedUnderSub> extends BinaryExpr<ExprType, ExprType, ExprType> {
	
	@Override
	public SubExpr<ExprType> withOps(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp);

	@Override
	public SubExpr<ExprType> withLeftOp(final Expr<? extends ExprType> leftOp);

	@Override
	public SubExpr<ExprType> withRightOp(final Expr<? extends ExprType> rightOp);
}