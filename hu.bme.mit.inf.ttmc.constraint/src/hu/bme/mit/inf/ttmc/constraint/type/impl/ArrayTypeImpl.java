package hu.bme.mit.inf.ttmc.constraint.type.impl;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractArrayType;

public final class ArrayTypeImpl<IndexType extends Type, ElemType extends Type>
		extends AbstractArrayType<IndexType, ElemType> {

	public ArrayTypeImpl(IndexType indexType, ElemType elemType) {
		super(indexType, elemType);
	}
}
