package hu.bme.mit.inf.ttmc.constraint.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.inf.ttmc.constraint.type.ArrayType;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.FuncType;
import hu.bme.mit.inf.ttmc.constraint.type.IntType;
import hu.bme.mit.inf.ttmc.constraint.type.RatType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class Types {

	private static final BoolType BOOL_TYPE;
	private static final IntType INT_TYPE;
	private static final RatType RAT_TYPE;

	static {
		BOOL_TYPE = new BoolTypeImpl();
		INT_TYPE = new IntTypeImpl();
		RAT_TYPE = new RatTypeImpl();
	}

	protected Types() {
	}

	public static BoolType Bool() {
		return BOOL_TYPE;
	}

	public static IntType Int() {
		return INT_TYPE;
	}

	public static RatType Rat() {
		return RAT_TYPE;
	}

	public static <P extends Type, R extends Type> FuncType<P, R> Func(final P paramTypes, final R resultType) {
		checkNotNull(paramTypes);
		checkNotNull(resultType);
		return new FuncTypeImpl<P, R>(paramTypes, resultType);
	}

	public static <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType) {
		checkNotNull(indexType);
		checkNotNull(elemType);
		return new ArrayTypeImpl<I, E>(indexType, elemType);
	}

}
