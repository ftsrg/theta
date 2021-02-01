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
import java.util.LinkedList;
import java.util.List;
import java.util.Optional;
import java.util.Random;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.Utils;

/**
 * A waitlist where items are removed in a random order.
 */
public final class RandomWaitlist<T> implements Waitlist<T> {

	private final List<T> items;
	private final Random random;

	private RandomWaitlist(final Optional<Long> seed) {
		items = new LinkedList<>();
		random = seed.isPresent() ? new Random(seed.get()) : new Random();
	}

	public static <T> RandomWaitlist<T> create() {
		return new RandomWaitlist<>(Optional.empty());
	}

	public static <T> RandomWaitlist<T> create(final long seed) {
		return new RandomWaitlist<>(Optional.of(seed));
	}

	@Override
	public void add(final T item) {
		items.add(checkNotNull(item));
	}

	@Override
	public void addAll(final Collection<? extends T> items) {

		this.items.addAll(checkNotNull(items));
	}

	@Override
	public void addAll(final Stream<? extends T> items) {
		checkNotNull(items);
		items.forEach(this.items::add);
	}

	@Override
	public boolean isEmpty() {
		return items.isEmpty();
	}

	@Override
	public T remove() {
		final int i = random.nextInt(items.size());
		return items.remove(i);
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
		return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(items).toString();
	}

}
