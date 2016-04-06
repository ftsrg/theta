package hu.bme.mit.inf.ttmc.constraint.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.constraint.type.impl.ArrayTypeImpl;
import hu.bme.mit.inf.ttmc.constraint.type.impl.BoolTypeImpl;
import hu.bme.mit.inf.ttmc.constraint.type.impl.FuncTypeImpl;
import hu.bme.mit.inf.ttmc.constraint.type.impl.IntTypeImpl;
import hu.bme.mit.inf.ttmc.constraint.type.impl.RatTypeImpl;

public class TypeFactoryImpl implements TypeFactory {

	final BoolType boolType;
	final IntType intType;
	final RatType ratType;

	private final ConstraintManager manager;

	public TypeFactoryImpl(final ConstraintManager manager) {
		this.manager = manager;

		boolType = new BoolTypeImpl(manager);
		intType = new IntTypeImpl(manager);
		ratType = new RatTypeImpl(manager);
	}

	@Override
	public BoolType Bool() {
		return boolType;
	}

	@Override
	public IntType Int() {
		return intType;
	}

	@Override
	public RatType Rat() {
		return ratType;
	}

	@Override
	public <P extends Type, R extends Type> FuncType<P, R> Func(final P paramTypes, final R resultType) {
		checkNotNull(paramTypes);
		checkNotNull(resultType);
		return new FuncTypeImpl<P, R>(manager, paramTypes, resultType);
	}

	@Override
	public <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType) {
		checkNotNull(indexType);
		checkNotNull(elemType);
		return new ArrayTypeImpl<I, E>(manager, indexType, elemType);
	}

}
