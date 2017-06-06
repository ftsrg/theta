package hu.bme.mit.theta.core.type.arraytype;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.type.Type;

public final class ArrayType<IndexType extends Type, ElemType extends Type> implements Type {

	private final static int HASH_SEED = 4919;
	private final static String TYPE_LABEL = "Array";

	private final IndexType indexType;
	private final ElemType elemType;

	private volatile int hashCode = 0;

	ArrayType(final IndexType indexType, final ElemType elemType) {
		this.indexType = checkNotNull(indexType);
		this.elemType = checkNotNull(elemType);
	}

	public IndexType getIndexType() {
		return indexType;
	}

	public ElemType getElemType() {
		return elemType;
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
