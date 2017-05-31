package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.type.Type;

public abstract class MultiaryExpr<OpsType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final List<Expr<OpsType>> ops;

	private volatile int hashCode = 0;

	protected MultiaryExpr(final Iterable<? extends Expr<OpsType>> ops) {
		this.ops = ImmutableList.copyOf(checkNotNull(ops));
	}

	public final List<Expr<OpsType>> getOps() {
		return ops;
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = getHashSeed();
			result = 31 * result + getOps().hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final String toString() {
		return ObjectUtils.toStringBuilder(getOperatorLabel()).addAll(ops).toString();
	}

	public abstract MultiaryExpr<OpsType, ExprType> withOps(final Iterable<? extends Expr<OpsType>> ops);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
