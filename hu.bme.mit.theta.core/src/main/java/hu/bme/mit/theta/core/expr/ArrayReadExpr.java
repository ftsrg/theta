package hu.bme.mit.theta.core.expr;

import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.Type;

public interface ArrayReadExpr<IndexType extends Type, ElemType extends Type> extends Expr<ElemType> {
	
	public Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> getArray();
	public Expr<? extends IndexType> getIndex();

	public ArrayReadExpr<IndexType, ElemType> with(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index);

	public ArrayReadExpr<IndexType, ElemType> withArray(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array);

	public ArrayReadExpr<IndexType, ElemType> withIndex(final Expr<? extends IndexType> index);

}