package hu.bme.mit.inf.ttmc.constraint.utils.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.type.Type;

public class TypeUtils {

	private TypeUtils() {
	}

	public static <T extends Type, T1 extends T, T2 extends T> Optional<T> join(final T1 type1, final T2 type2) {
		checkNotNull(type1);
		checkNotNull(type2);

		final Optional<? extends Type> join = type1.join(type2);
		@SuppressWarnings("unchecked")
		final Optional<T> result = (Optional<T>) join;
		return result;
	}

}
