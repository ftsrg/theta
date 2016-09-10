package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.Type;

public interface ArrayWriteExpr<IndexType extends Type, ElemType extends Type>
		extends Expr<ArrayType<IndexType, ElemType>> {

	public Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> getArray();

	public Expr<? extends IndexType> getIndex();

	public Expr<? extends ElemType> getElem();

	public ArrayWriteExpr<IndexType, ElemType> with(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Expr<? extends ElemType> elem);

	public default ArrayWriteExpr<IndexType, ElemType> withArray(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array) {
		return with(array, getIndex(), getElem());
	}

	public ArrayWriteExpr<IndexType, ElemType> withIndex(final Expr<? extends IndexType> index);

	public ArrayWriteExpr<IndexType, ElemType> withElem(final Expr<? extends ElemType> elem);

}