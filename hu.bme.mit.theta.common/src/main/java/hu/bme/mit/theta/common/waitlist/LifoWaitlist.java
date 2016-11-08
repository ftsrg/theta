package hu.bme.mit.theta.common.waitlist;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.stream.Stream;

import hu.bme.mit.theta.common.ObjectUtils;

/**
 * LIFO (Last In First Out) waitlist. Items are removed in the reverse order as
 * they were added.
 */
public class LifoWaitlist<T> implements Waitlist<T> {

	private final Deque<T> waitlist;

	public LifoWaitlist() {
		waitlist = new ArrayDeque<>();
	}

	public LifoWaitlist(final Collection<? extends T> items) {
		waitlist = new ArrayDeque<>(checkNotNull(items));
	}

	@Override
	public void add(final T item) {
		waitlist.push(item);
	}

	@Override
	public void addAll(final Collection<? extends T> items) {
		waitlist.addAll(checkNotNull(items));
	}

	@Override
	public boolean isEmpty() {
		return waitlist.isEmpty();
	}

	@Override
	public T remove() {
		return waitlist.pop();
	}

	@Override
	public void clear() {
		waitlist.clear();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("LifoWaitlist").addAll(waitlist).toString();
	}

	@Override
	public int size() {
		return waitlist.size();
	}

	@Override
	public void addAll(final Stream<? extends T> items) {
		items.forEach(waitlist::add);
	}
}
