package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;

public abstract class UnaryExpr<OpType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final Expr<OpType> op;

	private volatile int hashCode = 0;

	public UnaryExpr(final Expr<OpType> op) {
		this.op = checkNotNull(op);
	}

	public final Expr<OpType> getOp() {
		return op;
	}

	@Override
	public List<Expr<OpType>> getOps() {
		return ImmutableList.of(op);
	}

	@Override
	public int getArity() {
		return 1;
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

	public abstract UnaryExpr<OpType, ExprType> withOp(final Expr<OpType> op);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();
}
