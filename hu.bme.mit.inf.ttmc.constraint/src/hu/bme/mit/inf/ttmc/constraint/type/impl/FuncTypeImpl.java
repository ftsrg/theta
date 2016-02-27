package hu.bme.mit.inf.ttmc.constraint.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class FuncTypeImpl<ParamType extends Type, ResultType extends Type> extends AbstractType implements FuncType<ParamType, ResultType> {
	
	private final ParamType paramType;
	private final ResultType resultType;
	
	public FuncTypeImpl(final ParamType paramType, final ResultType resultType) {
		this.paramType = checkNotNull(paramType);
		this.resultType = checkNotNull(resultType);
	}
	
	@Override
	public ParamType getParamType() {
		return paramType;
	}

	@Override
	public ResultType getResultType() {
		return resultType;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Func(");
		sb.append(paramType);
		sb.append(" -> ");
		sb.append(resultType);
		sb.append(")");
		return sb.toString();
	}

}
