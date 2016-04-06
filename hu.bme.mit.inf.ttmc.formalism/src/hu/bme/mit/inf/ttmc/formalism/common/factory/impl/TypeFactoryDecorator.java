package hu.bme.mit.inf.ttmc.formalism.common.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public abstract class TypeFactoryDecorator implements TypeFactory {

	private final TypeFactory factory;
	
	public TypeFactoryDecorator(final TypeFactory factory) {
		checkNotNull(factory);
		this.factory = factory;
	}
	
	@Override
	public BoolType Bool() {
		return factory.Bool();
	}

	@Override
	public IntType Int() {
		return factory.Int();
	}

	@Override
	public RatType Rat() {
		return factory.Rat();
	}

	@Override
	public <P extends Type, R extends Type> FuncType<P, R> Func(P paramTypes, R resultType) {
		return factory.Func(paramTypes, resultType);
	}

	@Override
	public <I extends Type, E extends Type> ArrayType<I, E> Array(I indexType, E elemType) {
		return factory.Array(indexType, elemType);
	}

}
