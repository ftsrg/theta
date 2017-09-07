package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

public final class DispatchTable<R> {

	private final Map<Class<?>, Function<?, ? extends R>> cases;
	private final Function<Object, ? extends R> defaultCase;

	private DispatchTable(final Builder<R> builder) {
		this.cases = builder.cases;
		this.defaultCase = builder.defaultCase;
	}

	public <T> R dispatch(final T param) {
		final Class<?> clazz = param.getClass();
		@SuppressWarnings("unchecked")
		final Function<? super T, ? extends R> function = (Function<? super T, ? extends R>) cases.get(clazz);
		if (function == null) {
			return defaultCase.apply(param);
		} else {
			return function.apply(param);
		}
	}

	public static <R> Builder<R> builder() {
		return new Builder<>();
	}

	public static final class Builder<R> {

		private final Map<Class<?>, Function<?, ? extends R>> cases;
		private Function<Object, ? extends R> defaultCase;

		private boolean built;

		private Builder() {
			cases = new HashMap<>();
			defaultCase = null;
			built = false;
		}

		public <T> Builder<R> addCase(final Class<T> clazz, final Function<? super T, ? extends R> function) {
			checkState(!built, "Already built.");
			checkNotNull(clazz);
			checkNotNull(function);
			checkState(!cases.containsKey(clazz), "Class already present in the cases.");
			cases.put(clazz, function);
			return this;
		}

		public Builder<R> addDefault(final Function<Object, ? extends R> function) {
			checkState(!built, "Already built.");
			checkNotNull(function);
			checkState(defaultCase == null, "Default case already present.");
			defaultCase = function;
			return this;
		}

		public DispatchTable<R> build() {
			checkState(!built, "Already built.");
			built = true;
			if (defaultCase == null) {
				defaultCase = o -> {
					throw new AssertionError("Undefined default case executed");
				};
			}
			return new DispatchTable<>(this);
		}

	}

}
