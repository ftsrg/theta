package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.utils.TypeVisitor;

public abstract class AbstractArrayType<IndexType extends Type, ElemType extends Type> extends AbstractType
		implements ArrayType<IndexType, ElemType> {

	private final static int HASH_SEED = 4919;

	private final static String TYPE_LABEL = "Array";

	@SuppressWarnings("unused")
	private final ConstraintManager manager;

	private final IndexType indexType;
	private final ElemType elemType;

	private volatile int hashCode = 0;

	public AbstractArrayType(final ConstraintManager manager, final IndexType indexType, final ElemType elemType) {
		this.indexType = checkNotNull(indexType);
		this.elemType = checkNotNull(elemType);
		this.manager = manager;
	}

	@Override
	public final IndexType getIndexType() {
		return indexType;
	}

	@Override
	public final ElemType getElemType() {
		return elemType;
	}

	@Override
	public final <P, R> R accept(final TypeVisitor<? super P, ? extends R> visitor, final P param) {
		return visitor.visit(this, param);
	}

	@Override
	public final int hashCode() {
		if (hashCode == 0) {
			hashCode = HASH_SEED;
			hashCode = 31 * hashCode + indexType.hashCode();
			hashCode = 31 * hashCode + elemType.hashCode();
		}

		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
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
	public final String toString() {
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
