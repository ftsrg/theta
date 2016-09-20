package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.List;

public final class Utils {

	private Utils() {
	}

	public static <T> T singleElement(final Collection<? extends T> collection) {
		checkArgument(collection.size() == 1);
		return collection.iterator().next();
	}

	public static <T> T anyElement(final Collection<? extends T> collection) {
		checkArgument(collection.size() > 0);
		return collection.iterator().next();
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
