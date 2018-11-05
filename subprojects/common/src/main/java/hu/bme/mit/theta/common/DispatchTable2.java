/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.HashMap;
import java.util.Map;
import java.util.function.BiFunction;

public final class DispatchTable2<P, R> {

	private final Map<Class<?>, BiFunction<?, ? super P, ? extends R>> cases;
	private final BiFunction<Object, ? super P, ? extends R> defaultCase;

	private DispatchTable2(final Builder<P, R> builder) {
		this.cases = builder.cases;
		this.defaultCase = builder.defaultCase;
	}

	public <T> R dispatch(final T type, final P param) {
		final Class<?> clazz = type.getClass();
		@SuppressWarnings("unchecked")
		final BiFunction<? super T, ? super P, ? extends R> function = (BiFunction<? super T, ? super P, ? extends R>) cases
				.get(clazz);
		if (function == null) {
			return defaultCase.apply(type, param);
		} else {
			return function.apply(type, param);
		}
	}

	public static <P, R> Builder<P, R> builder() {
		return new Builder<>();
	}

	public static final class Builder<P, R> {

		private final Map<Class<?>, BiFunction<?, ? super P, ? extends R>> cases;
		private BiFunction<Object, ? super P, ? extends R> defaultCase;

		private boolean built;

		private Builder() {
			cases = new HashMap<>();
			defaultCase = null;
			built = false;
		}

		public <T> Builder<P, R> addCase(final Class<T> clazz,
				final BiFunction<? super T, ? super P, ? extends R> function) {
			checkState(!built, "Already built.");
			checkNotNull(clazz);
			checkNotNull(function);
			checkState(!cases.containsKey(clazz), "Class already present in the cases.");
			cases.put(clazz, function);
			return this;
		}

		public Builder<P, R> addDefault(final BiFunction<Object, ? super P, ? extends R> function) {
			checkState(!built, "Already built.");
			checkNotNull(function);
			checkState(defaultCase == null, "Default case already present.");
			defaultCase = function;
			return this;
		}

		public DispatchTable2<P, R> build() {
			checkState(!built, "Already built.");
			built = true;
			if (defaultCase == null) {
				defaultCase = (o, p) -> {
					throw new AssertionError("Undefined default case executed");
				};
			}
			return new DispatchTable2<>(this);
		}
	}
}
