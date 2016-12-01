package hu.bme.mit.theta.core.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.impl.Types.Array;

import java.util.Optional;

import hu.bme.mit.theta.core.expr.LitExpr;
import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.TypeVisitor;

final class ArrayTypeImpl<IndexType extends Type, ElemType extends Type> implements ArrayType<IndexType, ElemType> {

	private final static int HASH_SEED = 4919;

	private final static String TYPE_LABEL = "Array";

	private final IndexType indexType;
	private final ElemType elemType;

	private volatile int hashCode = 0;

	ArrayTypeImpl(final IndexType indexType, final ElemType elemType) {
		this.indexType = checkNotNull(indexType);
		this.elemType = checkNotNull(elemType);
	}

	@Override
	public IndexType getIndexType() {
		return indexType;
	}

	@Override
	public ElemType getElemType() {
		return elemType;
	}

	@Override
	public LitExpr<ArrayType<IndexType, ElemType>> getAny() {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public boolean isLeq(final Type type) {
		if (type instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) type;
			return that.getIndexType().isLeq(this.getIndexType()) && this.getElemType().isLeq(that.getElemType());
		} else {
			return false;
		}
	}

	@Override
	public Optional<ArrayType<?, ?>> meet(final Type type) {
		if (type instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) type;
			final Optional<? extends Type> joinOfIndexTypes = this.getIndexType().join(that.getIndexType());
			final Optional<? extends Type> meetOfElemTypes = this.getElemType().meet(that.getElemType());

			if (joinOfIndexTypes.isPresent() && meetOfElemTypes.isPresent()) {
				final ArrayType<?, ?> arrayType = Array(joinOfIndexTypes.get(), meetOfElemTypes.get());
				return Optional.of(arrayType);
			}
		}

		return Optional.empty();
	}

	@Override
	public Optional<ArrayType<?, ?>> join(final Type type) {
		if (type instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) type;
			final Optional<? extends Type> meetOfIndexTypes = this.getIndexType().meet(that.getIndexType());
			final Optional<? extends Type> joinOfElemTypes = this.getElemType().join(that.getElemType());

			if (meetOfIndexTypes.isPresent() && joinOfElemTypes.isPresent()) {
				final ArrayType<?, ?> arrayType = Array(meetOfIndexTypes.get(), joinOfElemTypes.get());
				return Optional.of(arrayType);
			}
		}

		return Optional.empty();
	}

	@Override
	public <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + indexType.hashCode();
			result = 31 * result + elemType.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof ArrayType<?, ?>) {
			final ArrayType<?, ?> that = (ArrayType<?, ?>) obj;
			return this.getIndexType().equals(that.getIndexType()) && this.getElemType().equals(that.getElemType());
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append(TYPE_LABEL);
		sb.append("(");
		sb.append(indexType);
		sb.append(" -> ");
		sb.append(elemType);
		sb.append(")");
		return sb.toString();
	}
}
