package hu.bme.mit.theta.formalism.common.type.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.Type;
import hu.bme.mit.theta.formalism.common.type.PointerType;

public final class Types2 {

	private Types2() {
	}

	public static <T extends Type> PointerType<T> Pointer(final T pointedType) {
		checkNotNull(pointedType);
		return new PointerTypeImpl<>(pointedType);
	}

}
