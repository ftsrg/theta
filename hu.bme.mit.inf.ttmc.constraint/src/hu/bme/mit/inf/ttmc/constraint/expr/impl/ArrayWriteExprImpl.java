package hu.bme.mit.inf.ttmc.constraint.expr.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.expr.defaults.AbstractExpr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public class ArrayWriteExprImpl<IndexType extends Type, ElemType extends Type>
		extends AbstractExpr<ArrayType<IndexType, ElemType>> implements ArrayWriteExpr<IndexType, ElemType> {

	private final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array;
	private final Expr<? extends IndexType> index;
	private final Expr<? extends ElemType> elem;

	public ArrayWriteExprImpl(final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Expr<? extends ElemType> elem) {

		this.array = checkNotNull(array);
		this.index = checkNotNull(index);
		this.elem = checkNotNull(elem);
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
	public Expr<? extends ElemType> getElem() {
		return elem;
	}

	@Override
	public ArrayWriteExpr<IndexType, ElemType> with(
			Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array, Expr<? extends IndexType> index,
			Expr<? extends ElemType> elem) {

		if (this.array == array && this.index == index && this.elem == elem) {
			return this;
		} else {
			return new ArrayWriteExprImpl<>(array, index, elem);
		}
	}

	@Override
	protected int getHashSeed() {
		return 1699;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Write(");
		sb.append(array);
		sb.append(", ");
		sb.append(index);
		sb.append(", ");
		sb.append(elem);
		sb.append(")");
		return sb.toString();
	}

	@Override
	public <P, R> R accept(ExprVisitor<? super P, ? extends R> visitor, P param) {
		return visitor.visit(this, param);
	}
	
	@Override
	public ArrayWriteExpr<IndexType, ElemType> withIndex(final Expr<? extends IndexType> index) {
		return with(getArray(), index, getElem());
	}

	@Override
	public ArrayWriteExpr<IndexType, ElemType> withElem(final Expr<? extends ElemType> elem) {
		return with(getArray(), getIndex(), elem);
	}
}
