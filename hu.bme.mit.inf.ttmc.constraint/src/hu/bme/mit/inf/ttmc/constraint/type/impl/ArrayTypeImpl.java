package hu.bme.mit.inf.ttmc.constraint.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class ArrayTypeImpl<IndexType extends Type, ElemType extends Type> extends AbstractType implements ArrayType<IndexType, ElemType> {
	
	private final IndexType indexType;
	private final ElemType elemType;
	
	public ArrayTypeImpl(final IndexType indexType, final ElemType elemType) {
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
