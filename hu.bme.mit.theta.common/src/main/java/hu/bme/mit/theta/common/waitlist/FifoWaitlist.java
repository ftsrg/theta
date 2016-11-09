package hu.bme.mit.theta.common.waitlist;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Queue;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.ObjectUtils;

/**
 * FIFO (First In First Out) waitlist. Items are removed in the same order as
 * they were added.
 */
public class FifoWaitlist<T> implements Waitlist<T> {

	private final Queue<T> items;

	public FifoWaitlist() {
		this.items = new ArrayDeque<>();
	}

	public FifoWaitlist(final Collection<? extends T> items) {
		this.items = new ArrayDeque<>(checkNotNull(items));
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
		return ObjectUtils.toStringBuilder("FifoWaitlist").addAll(items).toString();
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
