package hu.bme.mit.inf.ttmc.analysis.algorithm.impl.waitlist.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Queue;

import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.waitlist.Waitlist;

public class FIFOWaitlist<T> implements Waitlist<T> {

	private final Queue<T> waitlist;

	public FIFOWaitlist() {
		waitlist = new ArrayDeque<>();
	}

	public FIFOWaitlist(final Collection<? extends T> items) {
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
