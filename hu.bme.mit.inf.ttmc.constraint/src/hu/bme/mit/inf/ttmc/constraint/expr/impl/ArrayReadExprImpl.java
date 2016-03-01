package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ArrayReadExprImpl<IndexType extends Type, ElemType extends Type> extends AbstractExpr<ElemType>
		implements ArrayReadExpr<IndexType, ElemType> {

	private final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array;
	private final Expr<? extends IndexType> index;

	public ArrayReadExprImpl(final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index) {

		this.array = checkNotNull(array);
		this.index = checkNotNull(index);
	}

	@Override
	public Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> getArray() {
		return array;
	}

	@Override
	public Expr<? extends IndexType> getIndex() {
		return index;
	}

	@Override
	public ArrayReadExpr<IndexType, ElemType> with(
			Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array, Expr<? extends IndexType> index) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	protected int getHashSeed() {
		return 1321;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Read(");
		sb.append(array);
		sb.append(", ");
		sb.append(index);
		sb.append(")");
		return sb.toString();
	}

}
