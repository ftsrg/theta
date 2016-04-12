package hu.bme.mit.inf.ttmc.constraint.factory.impl;

import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.impl.Types;

public class TypeFactoryImpl implements TypeFactory {

	@Override
	public BoolType Bool() {
		return Types.Bool();
	}

	@Override
	public IntType Int() {
		return Types.Int();
	}

	@Override
	public RatType Rat() {
		return Types.Rat();
	}

	@Override
	public <P extends Type, R extends Type> FuncType<P, R> Func(final P paramTypes, final R resultType) {
		return Types.Func(paramTypes, resultType);
	}

	@Override
	public <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType) {
		return Types.Array(indexType, elemType);
	}

}
