package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;

public interface SubExpr<ExprType extends ClosedUnderSub> extends BinaryExpr<ExprType, ExprType, ExprType> {

	@Override
	SubExpr<ExprType> withOps(final Expr<? extends ExprType> leftOp, final Expr<? extends ExprType> rightOp);

	@Override
	SubExpr<ExprType> withLeftOp(final Expr<? extends ExprType> leftOp);

	@Override
	SubExpr<ExprType> withRightOp(final Expr<? extends ExprType> rightOp);
}