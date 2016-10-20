package hu.bme.mit.theta.common.waitlist;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Queue;

import hu.bme.mit.theta.common.ObjectUtils;

/**
 * FIFO (First In First Out) waitlist. Items are removed in the same order as
 * they were added.
 */
public class FifoWaitlist<T> implements Waitlist<T> {

	private final Queue<T> waitlist;

	public FifoWaitlist() {
		waitlist = new ArrayDeque<>();
	}

	public FifoWaitlist(final Collection<? extends T> items) {
		waitlist = new ArrayDeque<>(checkNotNull(items));
	}

	@Override
	public void add(final T item) {
		waitlist.add(item);
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
		return waitlist.remove();
	}

	@Override
	public void clear() {
		waitlist.clear();
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder("FifoWaitlist").addAll(waitlist).toString();
	}

	@Override
	public int size() {
		return waitlist.size();
	}
}
