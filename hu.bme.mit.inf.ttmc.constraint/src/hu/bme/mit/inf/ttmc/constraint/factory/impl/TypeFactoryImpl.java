package hu.bme.mit.inf.ttmc.constraint.factory.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.factory.TypeFactory;
import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.TupleType;
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
	
	public TypeFactoryImpl() {
		boolType = new BoolTypeImpl();
		intType = new IntTypeImpl();
		ratType = new RatTypeImpl();
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
	public TupleType Tuple(List<? extends Type> elemTypes) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@Override
	public <P extends Type, R extends Type> FuncType<P, R> Func(P paramTypes, R resultType) {
		checkNotNull(paramTypes);
		checkNotNull(resultType);
		return new FuncTypeImpl<P, R>(paramTypes, resultType);
	}

	@Override
	public <I extends Type, E extends Type> ArrayType<I, E> Array(I indexType, E elemType) {
		checkNotNull(indexType);
		checkNotNull(elemType);
		return new ArrayTypeImpl<I, E>(indexType, elemType);
	}

}
