package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;

public abstract class BinaryExpr<OpType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final Expr<OpType> leftOp;
	private final Expr<OpType> rightOp;

	private volatile int hashCode = 0;

	protected BinaryExpr(final Expr<OpType> leftOp, final Expr<OpType> rightOp) {
		this.leftOp = checkNotNull(leftOp);
		this.rightOp = checkNotNull(rightOp);
	}

	public final Expr<OpType> getLeftOp() {
		return leftOp;
	}

	public final Expr<OpType> getRightOp() {
		return rightOp;
	}

	@Override
	public final List<Expr<OpType>> getOps() {
		return ImmutableList.of(leftOp, rightOp);
	}

	@Override
	public final int getArity() {
		return 2;
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

	public abstract BinaryExpr<OpType, ExprType> withOps(final Expr<OpType> leftOp, final Expr<OpType> rightOp);

	public abstract BinaryExpr<OpType, ExprType> withLeftOp(final Expr<OpType> leftOp);

	public abstract BinaryExpr<OpType, ExprType> withRightOp(final Expr<OpType> rightOp);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
