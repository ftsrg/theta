package hu.bme.mit.theta.core.type.impl;

import java.util.List;

import hu.bme.mit.theta.core.type.ArrayType;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.FuncType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.ProcType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.UnitType;

public final class Types {

	private static final BoolType BOOL_TYPE = new BoolTypeImpl();
	private static final IntType INT_TYPE = new IntTypeImpl();
	private static final RatType RAT_TYPE = new RatTypeImpl();
	private static final UnitType UNIT_TYPE = new UnitTypeImpl();

	private Types() {
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

	public static UnitType Unit() {
		return UNIT_TYPE;
	}

	public static <P extends Type, R extends Type> FuncType<P, R> Func(final P paramType, final R resultType) {
		return new FuncTypeImpl<>(paramType, resultType);
	}

	public static <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType) {
		return new ArrayTypeImpl<>(indexType, elemType);
	}

	public static <R extends Type> ProcType<R> Proc(final List<? extends Type> paramTypes, final R returnType) {
		return new ProcTypeImpl<>(paramTypes, returnType);
	}

}
