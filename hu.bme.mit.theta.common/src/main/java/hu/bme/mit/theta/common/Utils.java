package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.Iterator;
import java.util.List;

public final class Utils {

	private Utils() {
	}

	public static <T> T singleElementOf(final Iterable<? extends T> collection) {
		final Iterator<? extends T> iterator = collection.iterator();
		checkArgument(iterator.hasNext());
		final T elem = iterator.next();
		checkArgument(!iterator.hasNext());
		return elem;
	}

	public static <T> T anyElementOf(final Collection<? extends T> collection) {
		final Iterator<? extends T> iterator = collection.iterator();
		checkArgument(iterator.hasNext());
		final T elem = iterator.next();
		return elem;
	}

	public static <T> T head(final List<? extends T> list) {
		checkArgument(!list.isEmpty());
		return list.get(0);
	}

	public static <T> List<? extends T> tail(final List<? extends T> list) {
		checkArgument(!list.isEmpty());
		return list.subList(1, list.size());
	}

}
