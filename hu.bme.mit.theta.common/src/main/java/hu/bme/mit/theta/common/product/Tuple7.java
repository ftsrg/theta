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
package hu.bme.mit.theta.common.product;

import com.google.common.collect.ImmutableList;

public final class Tuple7<T1, T2, T3, T4, T5, T6, T7> extends Tuple implements Product7<T1, T2, T3, T4, T5, T6, T7> {

	Tuple7(final T1 e1, final T2 e2, final T3 e3, final T4 e4, final T5 e5, final T6 e6, final T7 e7) {
		super(ImmutableList.of(e1, e2, e3, e4, e5, e6, e7));
	}

	@Override
	public T1 _1() {
		@SuppressWarnings("unchecked")
		final T1 result = (T1) elem(0);
		return result;
	}

	@Override
	public T2 _2() {
		@SuppressWarnings("unchecked")
		final T2 result = (T2) elem(1);
		return result;
	}

	@Override
	public T3 _3() {
		@SuppressWarnings("unchecked")
		final T3 result = (T3) elem(2);
		return result;
	}

	@Override
	public T4 _4() {
		@SuppressWarnings("unchecked")
		final T4 result = (T4) elem(3);
		return result;
	}

	@Override
	public T5 _5() {
		@SuppressWarnings("unchecked")
		final T5 result = (T5) elem(4);
		return result;
	}

	@Override
	public T6 _6() {
		@SuppressWarnings("unchecked")
		final T6 result = (T6) elem(5);
		return result;
	}

	@Override
	public T7 _7() {
		@SuppressWarnings("unchecked")
		final T7 result = (T7) elem(6);
		return result;
	}
}
