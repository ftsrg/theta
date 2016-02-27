package hu.bme.mit.inf.ttmc.constraint.z3.type;

import com.microsoft.z3.Context;
import com.microsoft.z3.Sort;

import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.impl.FuncTypeImpl;

public class Z3FuncType<ParamType extends Type, ResultType extends Type> extends FuncTypeImpl<ParamType, ResultType> implements Z3Type {

	@SuppressWarnings("unused")
	private final Context context;
	
	public Z3FuncType(final ParamType paramType, final ResultType resultType, final Context context) {
		super(paramType, resultType);
		this.context = context;
	}

	@Override
	public Sort getSort() {
		throw new UnsupportedOperationException();
	}
	
}
