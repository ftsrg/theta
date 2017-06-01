package hu.bme.mit.theta.core.type.arraytype;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.Type;

public final class ArrayExprs {

	private ArrayExprs() {
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayType<IndexType, ElemType> Array(
			final IndexType indexType, final ElemType elemType) {
		return new ArrayType<>(indexType, elemType);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayReadExpr<IndexType, ElemType> Read(
			final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index) {
		return new ArrayReadExpr<>(array, index);
	}

	public static <IndexType extends Type, ElemType extends Type> ArrayWriteExpr<IndexType, ElemType> Write(
			final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index, final Expr<ElemType> elem) {
		return new ArrayWriteExpr<>(array, index, elem);
	}

}
