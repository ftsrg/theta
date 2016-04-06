package hu.bme.mit.inf.ttmc.constraint.type.impl;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.defaults.AbstractFuncType;

public final class FuncTypeImpl<ParamType extends Type, ResultType extends Type>
		extends AbstractFuncType<ParamType, ResultType> {

	public FuncTypeImpl(final ConstraintManager manager, final ParamType paramType, final ResultType resultType) {
		super(manager, paramType, resultType);
	}

}