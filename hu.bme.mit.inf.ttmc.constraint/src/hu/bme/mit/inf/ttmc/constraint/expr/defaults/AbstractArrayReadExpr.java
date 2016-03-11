package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractArrayReadExpr<IndexType extends Type, ElemType extends Type>
		extends AbstractExpr<ElemType> implements ArrayReadExpr<IndexType, ElemType> {

	private final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array;
	private final Expr<? extends IndexType> index;

	public AbstractArrayReadExpr(final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
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
	public final ArrayReadExpr<IndexType, ElemType> with(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final ArrayReadExpr<IndexType, ElemType> withArray(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array) {
		return with(array, getIndex());
	}

	@Override
	public final ArrayReadExpr<IndexType, ElemType> withIndex(final Expr<? extends IndexType> index) {
		return with(getArray(), index);
	}

	@Override
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
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
		sb.append("Read(");
		sb.append(array);
		sb.append(", ");
		sb.append(index);
		sb.append(")");
		return sb.toString();
	}

	@Override
	protected final int getHashSeed() {
		return 1321;
	}

}
