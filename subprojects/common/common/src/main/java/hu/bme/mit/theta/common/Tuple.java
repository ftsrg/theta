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

import com.google.common.collect.ImmutableList;

import java.util.Iterator;
import java.util.List;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkPositionIndex;

public abstract class Tuple implements Iterable<Object> {

	private volatile int hashCode = 0;

	private final List<Object> elems;

	Tuple(final List<? extends Object> elems) {
		this.elems = ImmutableList.copyOf(checkNotNull(elems));
	}

	public final int arity() {
		return elems.size();
	}

	public final Object elem(final int n) {
		checkPositionIndex(n, arity());
		return elems.get(n);
	}

	public final List<?> toList() {
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
