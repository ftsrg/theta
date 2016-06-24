package hu.bme.mit.inf.ttmc.formalism.common.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.type.PointerType;
import hu.bme.mit.inf.ttmc.formalism.common.type.ProcType;
import hu.bme.mit.inf.ttmc.formalism.common.type.UnitType;

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

	public static <T extends Type> PointerType<T> Pointer(final T type) {
		checkNotNull(type);
		return new PointerTypeImpl<>(type);
	}

}
