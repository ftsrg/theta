package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractArrayType<IndexType extends Type, ElemType extends Type> extends AbstractType
		implements ArrayType<IndexType, ElemType> {

	private final static int HASH_SEED = 4919;

	private volatile int hashCode = 0;

	private final IndexType indexType;
	private final ElemType elemType;

	public AbstractArrayType(final IndexType indexType, final ElemType elemType) {
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
	public int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + indexType.hashCode();
			hashCode = 31 * hashCode + elemType.hashCode();
		}

		return hashCode;
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
		sb.append("Array(");
		sb.append(indexType);
		sb.append(" -> ");
		sb.append(elemType);
		sb.append(")");
		return sb.toString();
	}

}
