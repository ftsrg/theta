package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;

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

	public static ToStringBuilder toStringBuilder(final String prefix) {
		return new ToStringBuilder(prefix);
	}

}
