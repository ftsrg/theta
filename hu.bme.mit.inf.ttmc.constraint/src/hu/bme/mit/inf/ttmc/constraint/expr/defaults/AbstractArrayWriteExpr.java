package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractArrayWriteExpr<IndexType extends Type, ElemType extends Type>
		extends AbstractExpr<ArrayType<IndexType, ElemType>> implements ArrayWriteExpr<IndexType, ElemType> {

	private final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array;
	private final Expr<? extends IndexType> index;
	private final Expr<? extends ElemType> elem;

	public AbstractArrayWriteExpr(final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
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
	protected int getHashSeed() {
		return 1699;
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final ArrayWriteExpr<IndexType, ElemType> with(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Expr<? extends ElemType> elem) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final ArrayWriteExpr<IndexType, ElemType> withIndex(final Expr<? extends IndexType> index) {
		return with(getArray(), index, getElem());
	}

	@Override
	public final ArrayWriteExpr<IndexType, ElemType> withElem(final Expr<? extends ElemType> elem) {
		return with(getArray(), getIndex(), elem);
	}

	@Override
	public int hashCode() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean equals(final Object obj) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
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

}
