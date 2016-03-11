package hu.bme.mit.inf.ttmc.constraint.type.impl;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractFuncType;

public final class FuncTypeImpl<ParamType extends Type, ResultType extends Type> extends AbstractFuncType<ParamType, ResultType> {

	public FuncTypeImpl(ParamType paramType, ResultType resultType) {
		super(paramType, resultType);
	}
	
}