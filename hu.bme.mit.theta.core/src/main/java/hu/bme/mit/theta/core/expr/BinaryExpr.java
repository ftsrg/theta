package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.expr.BinaryExpr;
import hu.bme.mit.theta.core.type.Type;

/**
 * 
 * @author Tamas Toth
 *
 */
public interface BinaryExpr<LeftOpType extends Type, RightOpType extends Type, ExprType extends Type>
		extends Expr<ExprType> {
	
	public Expr<? extends LeftOpType> getLeftOp();

	public Expr<? extends RightOpType> getRightOp();

	public BinaryExpr<LeftOpType, RightOpType, ExprType> withOps(final Expr<? extends LeftOpType> leftOp, final Expr<? extends RightOpType> rightOp);

	public BinaryExpr<LeftOpType, RightOpType, ExprType> withLeftOp(final Expr<? extends LeftOpType> leftOp);

	public BinaryExpr<LeftOpType, RightOpType, ExprType> withRightOp(final Expr<? extends RightOpType> rightOp);
	
}
