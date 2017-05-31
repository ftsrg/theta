package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;

public abstract class BinaryExpr<LeftOpType extends Type, RightOpType extends Type, ExprType extends Type>
		implements Expr<ExprType> {

	private final Expr<LeftOpType> leftOp;
	private final Expr<RightOpType> rightOp;

	private volatile int hashCode = 0;

	protected BinaryExpr(final Expr<LeftOpType> leftOp, final Expr<RightOpType> rightOp) {
		this.leftOp = checkNotNull(leftOp);
		this.rightOp = checkNotNull(rightOp);
	}

	public final Expr<LeftOpType> getLeftOp() {
		return leftOp;
	}

	public final Expr<RightOpType> getRightOp() {
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
		return ObjectUtils.toStringBuilder(getOperatorLabel()).add(leftOp).add(rightOp).toString();
	}

	public abstract BinaryExpr<LeftOpType, RightOpType, ExprType> withOps(final Expr<LeftOpType> leftOp,
			final Expr<RightOpType> rightOp);

	public abstract BinaryExpr<LeftOpType, RightOpType, ExprType> withLeftOp(final Expr<LeftOpType> leftOp);

	public abstract BinaryExpr<LeftOpType, RightOpType, ExprType> withRightOp(final Expr<RightOpType> rightOp);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
