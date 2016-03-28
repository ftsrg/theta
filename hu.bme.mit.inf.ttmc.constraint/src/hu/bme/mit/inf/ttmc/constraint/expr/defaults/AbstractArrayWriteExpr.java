package hu.bme.mit.inf.ttmc.constraint.expr.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.ExprVisitor;

public abstract class AbstractArrayWriteExpr<IndexType extends Type, ElemType extends Type>
		extends AbstractExpr<ArrayType<IndexType, ElemType>> implements ArrayWriteExpr<IndexType, ElemType> {

	private static final int HASH_SEED = 1699;

	private static final String OPERATOR_LABEL = "Write";

	private final ConstraintManager manager;

	private volatile int hashCode = 0;

	private final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array;
	private final Expr<? extends IndexType> index;
	private final Expr<? extends ElemType> elem;

	public AbstractArrayWriteExpr(final ConstraintManager manager,
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Expr<? extends ElemType> elem) {
		this.manager = manager;

		this.array = checkNotNull(array);
		this.index = checkNotNull(index);
		this.elem = checkNotNull(elem);
	}

	@Override
	public final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> getArray() {
		return array;
	}

	@Override
	public final Expr<? extends IndexType> getIndex() {
		return index;
	}

	@Override
	public final Expr<? extends ElemType> getElem() {
		return elem;
	}

	@Override
	public final ArrayType<IndexType, ElemType> getType() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public final ArrayWriteExpr<IndexType, ElemType> with(
			final Expr<? extends ArrayType<? super IndexType, ? extends ElemType>> array,
			final Expr<? extends IndexType> index, final Expr<? extends ElemType> elem) {

		if (this.array == array && this.index == index && elem == this.elem) {
			return this;
		} else {
			return manager.getExprFactory().Write(array, index, elem);
		}
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
	public final <P, R> R accept(final ExprVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + array.hashCode();
			result = 31 * result + index.hashCode();
			result = 31 * result + elem.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ArrayWriteExpr<?, ?>) {
			final ArrayWriteExpr<?, ?> that = (ArrayWriteExpr<?, ?>) obj;
			return this.getArray().equals(that.getArray()) && this.getIndex().equals(that.getIndex())
					&& this.getElem().equals(that.getElem());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(OPERATOR_LABEL);
		sb.append("(");
		sb.append(array);
		sb.append(", ");
		sb.append(index);
		sb.append(", ");
		sb.append(elem);
		sb.append(")");
		return sb.toString();
	}

}
