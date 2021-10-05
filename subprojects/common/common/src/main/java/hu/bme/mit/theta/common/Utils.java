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

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;

import static com.google.common.base.Preconditions.checkArgument;

public final class Utils {

	private Utils() {
	}

	public static <T> T singleElementOf(final Iterable<? extends T> collection) {
		final Iterator<? extends T> iterator = collection.iterator();
		checkArgument(iterator.hasNext(), "No elements collection");
		final T elem = iterator.next();
		checkArgument(!iterator.hasNext(), "More than one elements in collection");
		return elem;
	}

	public static <T> T anyElementOf(final Collection<? extends T> collection) {
		final Iterator<? extends T> iterator = collection.iterator();
		checkArgument(iterator.hasNext(), "No elements collection");
		final T elem = iterator.next();
		return elem;
	}

	public static <T> T head(final List<? extends T> list) {
		checkArgument(!list.isEmpty(), "Empty list");
		return list.get(0);
	}

	public static <T> List<T> tail(final List<T> list) {
		checkArgument(!list.isEmpty(), "Empty list");
		return list.subList(1, list.size());
	}

	////

	public static <T> boolean anyMatch(final Optional<T> optional, final Predicate<? super T> predicate) {
		if (optional.isPresent()) {
			return predicate.test(optional.get());
		} else {
			return false;
		}
	}

	public static <T> boolean allMatch(final Optional<T> optional, final Predicate<? super T> predicate) {
		if (optional.isPresent()) {
			return predicate.test(optional.get());
		} else {
			return true;
		}
	}

	public static LispStringBuilder lispStringBuilder() {
		return lispStringBuilder("");
	}

	public static LispStringBuilder lispStringBuilder(final String prefix) {
		return new LispStringBuilder(prefix);
	}

}
