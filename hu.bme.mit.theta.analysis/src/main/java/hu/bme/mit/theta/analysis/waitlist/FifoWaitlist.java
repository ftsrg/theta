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
package hu.bme.mit.theta.analysis.waitlist;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Queue;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.Utils;

/**
 * FIFO (First In First Out) waitlist. Items are removed in the same order as
 * they were added.
 */
public final class FifoWaitlist<T> implements Waitlist<T> {

	private final Queue<T> items;

	private FifoWaitlist(final Collection<? extends T> items) {
		this.items = new ArrayDeque<>(checkNotNull(items));
	}

	public static <T> FifoWaitlist<T> create(final Collection<? extends T> items) {
		return new FifoWaitlist<>(items);
	}

	public static <T> FifoWaitlist<T> create() {
		return new FifoWaitlist<>(Collections.emptySet());
	}

	@Override
	public void add(final T item) {
		items.add(item);
	}

	@Override
	public void addAll(final Collection<? extends T> items) {
		this.items.addAll(checkNotNull(items));
	}

	@Override
	public boolean isEmpty() {
		return items.isEmpty();
	}

	@Override
	public T remove() {
		return items.remove();
	}

	@Override
	public void clear() {
		items.clear();
	}

	@Override
	public String toString() {
		return Utils.toStringBuilder(getClass().getSimpleName()).addAll(items).toString();
	}

	@Override
	public int size() {
		return items.size();
	}

	@Override
	public void addAll(final Stream<? extends T> items) {
		checkNotNull(items);
		items.forEach(this::add);
	}
}
