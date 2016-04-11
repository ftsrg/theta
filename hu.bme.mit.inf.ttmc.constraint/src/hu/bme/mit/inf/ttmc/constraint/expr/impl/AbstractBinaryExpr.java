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

	protected AbstractBinaryExpr(final Expr<? extends LeftOpType> leftOp, final Expr<? extends RightOpType> rightOp) {
		this.leftOp = checkNotNull(leftOp);
		this.rightOp = checkNotNull(rightOp);
	}

	@Override
	public final Expr<? extends LeftOpType> getLeftOp() {
		return leftOp;
	}

	@Override
	public final Expr<? extends RightOpType> getRightOp() {
		return rightOp;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + getLeftOp().hashCode();
			result = 31 * result + getRightOp().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(getOperatorLabel());
		sb.append("(");
		sb.append(leftOp.toString());
		sb.append(", ");
		sb.append(rightOp.toString());
		sb.append(")");
		return sb.toString();
	}

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
