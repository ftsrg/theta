package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

public class LifoWaitlist<T> implements Waitlist<T> {

	private final Deque<T> waitlist;

	public LifoWaitlist() {
		waitlist = new ArrayDeque<>();
	}

	public LifoWaitlist(final Collection<? extends T> items) {
		waitlist = new ArrayDeque<>(items);
	}

	@Override
	public void add(final T item) {
		waitlist.push(checkNotNull(item));
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
		return waitlist.pop();
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
