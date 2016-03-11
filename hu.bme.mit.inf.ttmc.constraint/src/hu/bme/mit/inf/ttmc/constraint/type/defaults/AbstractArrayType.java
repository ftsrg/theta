package hu.bme.mit.inf.ttmc.constraint.type.defaults;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class AbstractArrayType<IndexType extends Type, ElemType extends Type> extends AbstractType implements ArrayType<IndexType, ElemType> {
	
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
