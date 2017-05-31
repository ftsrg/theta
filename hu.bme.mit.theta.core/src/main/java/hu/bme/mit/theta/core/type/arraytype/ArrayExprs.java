package hu.bme.mit.theta.core.type.arraytype;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class ArrayExprs {

	private ArrayExprs() {
	}

	public static <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType) {
		return new ArrayType<>(indexType, elemType);
	}

	public static <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(final Expr<ArrayType<I, E>> array,
			final Expr<I> index) {
		return new ArrayReadExpr<>(array, index);
	}

	public static <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(final Expr<ArrayType<I, E>> array,
			final Expr<I> index, final Expr<E> elem) {
		return new ArrayWriteExpr<>(array, index, elem);
	}

}
