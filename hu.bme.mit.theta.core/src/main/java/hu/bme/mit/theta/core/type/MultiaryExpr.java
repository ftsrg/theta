package hu.bme.mit.theta.core.type;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.utils.TypeUtils;

public abstract class MultiaryExpr<OpType extends Type, ExprType extends Type> implements Expr<ExprType> {

	private final List<Expr<OpType>> ops;

	private volatile int hashCode = 0;

	protected MultiaryExpr(final Iterable<? extends Expr<OpType>> ops) {
		checkNotNull(ops);
		this.ops = ImmutableList.copyOf(ops);
		checkArgument(this.ops.size() > 0);
	}

	@Override
	public final int getArity() {
		return ops.size();
	}

	@Override
	public final List<Expr<OpType>> getOps() {
		return ops;
	}

	@Override
	public final MultiaryExpr<OpType, ExprType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		final OpType opType = getOps().get(0).getType();
		final List<Expr<OpType>> newOps = ops.stream().map(op -> TypeUtils.cast(op, opType)).collect(toImmutableList());
		return with(newOps);
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
		return Utils.toStringBuilder(getOperatorLabel()).addAll(ops).toString();
	}

	public abstract MultiaryExpr<OpType, ExprType> with(final Iterable<? extends Expr<OpType>> ops);

	protected abstract int getHashSeed();

	protected abstract String getOperatorLabel();

}
