package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.Type;


public abstract class AbstractBinaryExpr<LeftOpType extends Type, RightOpType extends Type, ExprType extends Type>
		extends AbstractExpr<ExprType> implements BinaryExpr<LeftOpType, RightOpType, ExprType> {

	private final Expr<? extends LeftOpType> leftOp;
	private final Expr<? extends RightOpType> rightOp;

	private volatile int hashCode = 0;

	protected AbstractBinaryExpr(final Expr<? extends LeftOpType> leftOp,
			final Expr<? extends RightOpType> rightOp) {
		this.leftOp = checkNotNull(leftOp);
		this.rightOp = checkNotNull(rightOp);
	}

	@Override
	public Expr<? extends LeftOpType> getLeftOp() {
		return leftOp;
	}

	@Override
	public Expr<? extends RightOpType> getRightOp() {
		return rightOp;
	}

	@Override
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = getHashSeed();
			hashCode = 31 * hashCode + getLeftOp().hashCode();
			hashCode = 31 * hashCode + getRightOp().hashCode();
		}

		return hashCode;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final AbstractBinaryExpr<?, ?, ?> that = (AbstractBinaryExpr<?, ?, ?>) obj;
			return leftOp.equals(that.leftOp) && this.rightOp.equals(that.rightOp);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getOperatorString());
		sb.append("(");
		sb.append(leftOp.toString());
		sb.append(", ");
		sb.append(rightOp.toString());
		sb.append(")");
		return sb.toString();
	}

	protected abstract String getOperatorString();
	
	@Override
	public BinaryExpr<LeftOpType, RightOpType, ExprType> withLeftOp(final Expr<? extends LeftOpType> leftOp) {
		return withOps(leftOp, getRightOp());
	}

	@Override
	public BinaryExpr<LeftOpType, RightOpType, ExprType> withRightOp(final Expr<? extends RightOpType> rightOp) {
		return withOps(getLeftOp(), rightOp);
	}

}
