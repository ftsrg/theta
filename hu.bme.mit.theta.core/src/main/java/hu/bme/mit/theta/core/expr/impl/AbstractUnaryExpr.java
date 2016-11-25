package hu.bme.mit.theta.core.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.UnaryExpr;
import hu.bme.mit.theta.core.type.Type;

public abstract class AbstractUnaryExpr<OpType extends Type, ExprType extends Type> extends AbstractExpr<ExprType>
		implements UnaryExpr<OpType, ExprType> {

	private final Expr<? extends OpType> op;

	private volatile int hashCode = 0;

	public AbstractUnaryExpr(final Expr<? extends OpType> op) {
		this.op = checkNotNull(op);
	}

	@Override
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

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();
}
