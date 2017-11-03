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
import static java.util.Arrays.asList;

import java.util.StringJoiner;
import java.util.function.Function;

/**
 * Utility class for printing Lisp style strings, e.g., (A (B 1 2) (C 3)).
 */
public final class LispStringBuilder {

	private final StringJoiner joiner;

	LispStringBuilder(final String prefix) {
		checkNotNull(prefix);
		joiner = new StringJoiner(" ", "(", ")");
		if (!"".equals(prefix)) {
			joiner.add(prefix);
		}
	}

	public LispStringBuilder add(final Object object) {
		joiner.add(object.toString());
		return this;
	}

	public LispStringBuilder addAll(final Iterable<? extends Object> objects) {
		objects.forEach(o -> joiner.add(o.toString()));
		return this;
	}

	public <T> LispStringBuilder addAll(final Iterable<? extends T> objects, final Function<T, String> toStringFunc) {
		objects.forEach(o -> joiner.add(toStringFunc.apply(o)));
		return this;
	}

	public LispStringBuilder addAll(final Object... objects) {
		addAll(asList(objects));
		return this;
	}

	@Override
	public String toString() {
		return joiner.toString();
	}

}
