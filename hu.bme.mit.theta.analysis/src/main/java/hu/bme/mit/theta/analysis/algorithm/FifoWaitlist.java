package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Queue;

public class FifoWaitlist<T> implements Waitlist<T> {

	private final Queue<T> waitlist;

	public FifoWaitlist() {
		waitlist = new ArrayDeque<>();
	}

	public FifoWaitlist(final Collection<? extends T> items) {
		waitlist = new ArrayDeque<>(items);
	}

	@Override
	public void add(final T item) {
		waitlist.add(checkNotNull(item));
	}

	@Override
	public void addAll(final Collection<? extends T> items) {
		waitlist.addAll(items);
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
		return waitlist.toString();
	}
}
