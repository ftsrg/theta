package hu.bme.mit.theta.core.type.arraytype;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.Type;

public final class ArrayExprs {

	private ArrayExprs() {
	}

	public static <I extends Type, E extends Type> ArrayReadExpr<I, E> Read(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index) {
		return new ArrayReadExpr<>(array, index);
	}

	public static <I extends Type, E extends Type> ArrayWriteExpr<I, E> Write(
			final Expr<? extends ArrayType<? super I, ? extends E>> array, final Expr<? extends I> index,
			final Expr<? extends E> elem) {
		return new ArrayWriteExpr<>(array, index, elem);
	}

}
