package hu.bme.mit.theta.core.type;

import java.util.List;

public final class Types {

	private Types() {
	}

	public static IntType Int() {
		return IntType.getInstance();
	}

	public static RatType Rat() {
		return RatType.getInstance();
	}

	public static UnitType Unit() {
		return UnitType.getInstance();
	}

	public static <P extends Type, R extends Type> FuncType<P, R> Func(final P paramType, final R resultType) {
		return new FuncType<>(paramType, resultType);
	}

	public static <I extends Type, E extends Type> ArrayType<I, E> Array(final I indexType, final E elemType) {
		return new ArrayType<>(indexType, elemType);
	}

	public static <R extends Type> ProcType<R> Proc(final List<? extends Type> paramTypes, final R returnType) {
		return new ProcType<>(paramTypes, returnType);
	}

}
