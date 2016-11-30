package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.Type;

public interface ArrayWriteExpr<IndexType extends Type, ElemType extends Type>
		extends Expr<ArrayType<IndexType, ElemType>> {

	Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> getArray();

	Expr<? extends IndexType> getIndex();

	Expr<? extends ElemType> getElem();

	ArrayWriteExpr<IndexType, ElemType> with(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Expr<? extends ElemType> elem);

	default ArrayWriteExpr<IndexType, ElemType> withArray(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array) {
		return with(array, getIndex(), getElem());
	}

	ArrayWriteExpr<IndexType, ElemType> withIndex(final Expr<? extends IndexType> index);

	ArrayWriteExpr<IndexType, ElemType> withElem(final Expr<? extends ElemType> elem);

}