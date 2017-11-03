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

import java.util.Collection;
import java.util.Comparator;
import java.util.PriorityQueue;
import java.util.stream.Stream;

import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.common.Utils;

/**
 * Priority waitlist. The least item is always removed based on a comparator or
 * on the natural ordering (if no comparator is given).
 *
 * @see ArgNodeComparators
 */
public final class PriorityWaitlist<T> implements Waitlist<T> {

	private final PriorityQueue<T> items;

	private PriorityWaitlist(final Comparator<? super T> comparator) {
		items = new PriorityQueue<>(checkNotNull(comparator));
	}

	private PriorityWaitlist() {
		items = new PriorityQueue<>();
	}

	public static <T> PriorityWaitlist<T> create(final Comparator<? super T> comparator) {
		return new PriorityWaitlist<>(comparator);
	}

	public static <T> PriorityWaitlist<T> create() {
		return new PriorityWaitlist<>();
	}

	@Override
	public void add(final T item) {
		items.add(item);
	}

	@Override
	public void addAll(final Collection<? extends T> items) {
		checkNotNull(items);
		items.forEach(this::add);
	}

	@Override
	public void addAll(final Stream<? extends T> items) {
		checkNotNull(items);
		items.forEach(this::add);
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
	public int size() {
		return items.size();
	}

	@Override
	public void clear() {
		items.clear();
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).add(items.comparator()).addAll(items).toString();
	}
}
