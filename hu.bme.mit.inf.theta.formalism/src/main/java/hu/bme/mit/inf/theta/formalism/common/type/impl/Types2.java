package hu.bme.mit.inf.theta.formalism.common.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.type.PointerType;
import hu.bme.mit.inf.theta.formalism.common.type.ProcType;
import hu.bme.mit.inf.theta.formalism.common.type.UnitType;

public class Types2 {

	private static final UnitType UNIT_TYPE;

	static {
		UNIT_TYPE = new UnitTypeImpl();
	}

	private Types2() {
	}

	public static UnitType Unit() {
		return UNIT_TYPE;
	}

	public static <R extends Type> ProcType<R> Proc(final List<? extends Type> paramTypes, final R resultType) {
		checkNotNull(paramTypes);
		checkNotNull(resultType);
		return new ProcTypeImpl<>(paramTypes, resultType);
	}

	public static <T extends Type> PointerType<T> Pointer(final T pointedType) {
		checkNotNull(pointedType);
		return new PointerTypeImpl<>(pointedType);
	}

}
