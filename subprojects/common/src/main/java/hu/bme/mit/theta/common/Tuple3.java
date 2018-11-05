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

import com.google.common.collect.ImmutableList;

public final class Tuple3<T1, T2, T3> extends Tuple {

	private Tuple3(final T1 e1, final T2 e2, final T3 e3) {
		super(ImmutableList.of(e1, e2, e3));
	}

	public static <T1, T2, T3> Tuple3<T1, T2, T3> of(final T1 e1, final T2 e2, final T3 e3) {
		return new Tuple3<>(e1, e2, e3);
	}

	public T1 get1() {
		@SuppressWarnings("unchecked")
		final T1 result = (T1) elem(0);
		return result;
	}

	public T2 get2() {
		@SuppressWarnings("unchecked")
		final T2 result = (T2) elem(1);
		return result;
	}

	public T3 get3() {
		@SuppressWarnings("unchecked")
		final T3 result = (T3) elem(2);
		return result;
	}

	public <R> R unpackTo(final TriFunction<? super T1, ? super T2, ? super T3, ? extends R> function) {
		checkNotNull(function);
		return function.apply(get1(), get2(), get3());
	}

}
