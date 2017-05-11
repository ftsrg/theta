package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;

public abstract class UnaryExpr<OpType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final Expr<? extends OpType> op;

	private volatile int hashCode = 0;

	public UnaryExpr(final Expr<? extends OpType> op) {
		this.op = checkNotNull(op);
	}

	public final Expr<? extends OpType> getOp() {
		return op;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 37 * result + getOp().hashCode();
			result = hashCode;
		}
		return result;
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder(getOperatorLabel()).add(op).toString();
	}

	public abstract UnaryExpr<OpType, ExprType> withOp(final Expr<? extends OpType> op);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();
}
