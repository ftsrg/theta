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

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkPositionIndex;

import java.util.Iterator;
import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.common.Utils;

public abstract class Tuple implements Product, Iterable<Object> {

	private volatile int hashCode = 0;

	private final List<Object> elems;

	Tuple(final List<? extends Object> elems) {
		this.elems = ImmutableList.copyOf(checkNotNull(elems));
	}

	////

	public static <T1, T2> Tuple2<T1, T2> of(final T1 e1, final T2 e2) {
		return new Tuple2<>(e1, e2);
	}

	public static <T1, T2, T3> Tuple3<T1, T2, T3> of(final T1 e1, final T2 e2, final T3 e3) {
		return new Tuple3<>(e1, e2, e3);
	}

	public static <T1, T2, T3, T4> Tuple4<T1, T2, T3, T4> of(final T1 e1, final T2 e2, final T3 e3, final T4 e4) {
		return new Tuple4<>(e1, e2, e3, e4);
	}

	public static <T1, T2, T3, T4, T5> Tuple5<T1, T2, T3, T4, T5> of(final T1 e1, final T2 e2, final T3 e3, final T4 e4,
			final T5 e5) {
		return new Tuple5<>(e1, e2, e3, e4, e5);
	}

	public static <T1, T2, T3, T4, T5, T6> Tuple6<T1, T2, T3, T4, T5, T6> of(final T1 e1, final T2 e2, final T3 e3,
			final T4 e4, final T5 e5, final T6 e6) {
		return new Tuple6<>(e1, e2, e3, e4, e5, e6);
	}

	public static <T1, T2, T3, T4, T5, T6, T7> Tuple7<T1, T2, T3, T4, T5, T6, T7> of(final T1 e1, final T2 e2,
			final T3 e3, final T4 e4, final T5 e5, final T6 e6, final T7 e7) {
		return new Tuple7<>(e1, e2, e3, e4, e5, e6, e7);
	}

	////

	@Override
	public final int arity() {
		return elems.size();
	}

	@Override
	public final Object elem(final int n) {
		checkPositionIndex(n, arity());
		return elems.get(n);
	}

	@Override
	public final List<Object> toList() {
		return elems;
	}

	@Override
	public final Iterator<Object> iterator() {
		return elems.iterator();
	}

	////

	@Override
	public final int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = arity();
			result = 31 * result + elems.hashCode();
			hashCode = result;
		}
		return hashCode;
	}

	@Override
	public final boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (this.getClass() == obj.getClass()) {
			final Tuple that = (Tuple) obj;
			return this.elems.equals(that.elems);
		} else {
			return false;
		}
	}

	@Override
	public final String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(elems).toString();
	}

}
