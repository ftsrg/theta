package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.Type;

/**
 *
 * @author Tamas Toth
 *
 */
public interface BinaryExpr<LeftOpType extends Type, RightOpType extends Type, ExprType extends Type>
		extends Expr<ExprType> {

	Expr<? extends LeftOpType> getLeftOp();

	Expr<? extends RightOpType> getRightOp();

	BinaryExpr<LeftOpType, RightOpType, ExprType> withOps(final Expr<? extends LeftOpType> leftOp,
			final Expr<? extends RightOpType> rightOp);

	BinaryExpr<LeftOpType, RightOpType, ExprType> withLeftOp(final Expr<? extends LeftOpType> leftOp);

	BinaryExpr<LeftOpType, RightOpType, ExprType> withRightOp(final Expr<? extends RightOpType> rightOp);

}
