package hu.bme.mit.theta.common.waitlist;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.ObjectUtils;

/**
 * LIFO (Last In First Out) waitlist. Items are removed in the reverse order as
 * they were added.
 */
public class LifoWaitlist<T> implements Waitlist<T> {

	private final Deque<T> items;

	private LifoWaitlist(final Collection<? extends T> items) {
		this.items = new ArrayDeque<>(checkNotNull(items));
	}

	public static <T> LifoWaitlist<T> create() {
		return new LifoWaitlist<>(Collections.emptySet());
	}

	public static <T> LifoWaitlist<T> create(final Collection<? extends T> items) {
		return new LifoWaitlist<>(items);
	}

	@Override
	public void add(final T item) {
		items.push(item);
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
		return items.pop();
	}

	@Override
	public void clear() {
		items.clear();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("LifoWaitlist").addAll(items).toString();
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
