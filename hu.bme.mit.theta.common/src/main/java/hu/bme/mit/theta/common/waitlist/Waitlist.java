package hu.bme.mit.theta.common.waitlist;

import java.util.Collection;
import java.util.stream.Stream;

/**
 * Generic interface for waitlists. Elements added to a waitlist are removed in
 * a specific order that the implementations determine.
 */
public interface Waitlist<T> {
	void add(T item);

	void addAll(Collection<? extends T> items);

	void addAll(Stream<? extends T> items);

	boolean isEmpty();

	T remove();

	int size();

	void clear();
}
