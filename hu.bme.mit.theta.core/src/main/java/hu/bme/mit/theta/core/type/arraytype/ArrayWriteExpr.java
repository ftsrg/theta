package hu.bme.mit.theta.core.type.arraytype;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Array;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.core.LitExpr;
import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.utils.TypeUtils;

public final class ArrayWriteExpr<IndexType extends Type, ElemType extends Type>
		implements Expr<ArrayType<IndexType, ElemType>> {

	private static final int HASH_SEED = 1699;

	private static final String OPERATOR_LABEL = "Write";

	private volatile int hashCode = 0;

	private final Expr<ArrayType<IndexType, ElemType>> array;
	private final Expr<IndexType> index;
	private final Expr<ElemType> elem;

	ArrayWriteExpr(final Expr<ArrayType<IndexType, ElemType>> array, final Expr<IndexType> index,
			final Expr<ElemType> elem) {
		this.array = checkNotNull(array);
		this.index = checkNotNull(index);
		this.elem = checkNotNull(elem);
	}

	public Expr<ArrayType<IndexType, ElemType>> getArray() {
		return array;
	}

	public Expr<IndexType> getIndex() {
		return index;
	}

	public Expr<ElemType> getElem() {
		return elem;
	}

	@Override
	public ArrayType<IndexType, ElemType> getType() {
		return Array(index.getType(), elem.getType());
	}

	@Override
	public LitExpr<ArrayType<IndexType, ElemType>> eval(final Valuation val) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public int getArity() {
		return 3;
	}

	@Override
	public List<? extends Expr<?>> getOps() {
		return ImmutableList.of(array, index, elem);
	}

	@Override
	public Expr<ArrayType<IndexType, ElemType>> withOps(final List<? extends Expr<?>> ops) {
		checkNotNull(ops);
		checkArgument(ops.size() == 3);
		final Expr<ArrayType<IndexType, ElemType>> newArray = TypeUtils.cast(ops.get(0), array.getType());
		final Expr<IndexType> newIndex = TypeUtils.cast(ops.get(0), index.getType());
		final Expr<ElemType> newElem = TypeUtils.cast(ops.get(2), elem.getType());
		return with(newArray, newIndex, newElem);
	}

	public ArrayWriteExpr<IndexType, ElemType> with(final Expr<ArrayType<IndexType, ElemType>> array,
			final Expr<IndexType> index, final Expr<ElemType> elem) {
		if (this.array == array && this.index == index && elem == this.elem) {
			return this;
		} else {
			return new ArrayWriteExpr<>(array, index, elem);
		}
	}

	public ArrayWriteExpr<IndexType, ElemType> withIndex(final Expr<IndexType> index) {
		return with(getArray(), index, getElem());
	}

	public ArrayWriteExpr<IndexType, ElemType> withElem(final Expr<ElemType> elem) {
		return with(getArray(), getIndex(), elem);
	}

	@Override
	public int hashCode() {
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
	public boolean equals(final Object obj) {
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
		return ObjectUtils.toStringBuilder(OPERATOR_LABEL).add(array).add(index).add(elem).toString();
	}

}
