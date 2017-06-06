package hu.bme.mit.theta.core;

import static com.google.common.collect.ImmutableList.toImmutableList;

import java.util.List;
import java.util.function.Function;

public interface Expr<ExprType extends Type> {

	ExprType getType();

	int getArity();

	List<? extends Expr<?>> getOps();

	Expr<ExprType> withOps(List<? extends Expr<?>> ops);

	public default <T extends Type> Expr<ExprType> rewrite(
			final Function<? super Expr<T>, ? extends Expr<T>> function) {
		return this.withOps(this.getOps().stream().map(op -> op.rewrite(function)).collect(toImmutableList()));
	}

}