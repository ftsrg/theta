package hu.bme.mit.theta.analysis.algorithm;

import java.util.Collection;

/**
 * Generic interface for waitlists. Elements added to a waitlist are removed in
 * a specific order that the implementations determine.
 */
public interface Waitlist<T> {
	void add(T item);

	void addAll(Collection<? extends T> items);

	boolean isEmpty();

	T remove();

	int size();

	void clear();
}
