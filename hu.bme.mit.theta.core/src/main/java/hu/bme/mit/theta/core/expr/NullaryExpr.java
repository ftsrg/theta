package hu.bme.mit.theta.core.expr;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.type.Type;

public abstract class NullaryExpr<ExprType extends Type> implements Expr<ExprType> {

	@Override
	public final List<Expr<?>> getOps() {
		return ImmutableList.of();
	}

	@Override
	public final NullaryExpr<ExprType> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.isEmpty());
		return this;
	}

	@Override
	public final int getArity() {
		return 0;
	}

}
