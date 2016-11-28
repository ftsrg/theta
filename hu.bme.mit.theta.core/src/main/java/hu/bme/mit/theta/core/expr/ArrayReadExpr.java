package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.Type;

public interface ArrayReadExpr<IndexType extends Type, ElemType extends Type> extends Expr<ElemType> {

	Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> getArray();

	Expr<? extends IndexType> getIndex();

	ArrayReadExpr<IndexType, ElemType> with(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index);

	ArrayReadExpr<IndexType, ElemType> withArray(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array);

	ArrayReadExpr<IndexType, ElemType> withIndex(final Expr<? extends IndexType> index);

}