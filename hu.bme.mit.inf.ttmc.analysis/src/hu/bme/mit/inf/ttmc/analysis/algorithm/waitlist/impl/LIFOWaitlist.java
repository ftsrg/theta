package hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.Waitlist;

public class LIFOWaitlist<S extends State> implements Waitlist<S> {

	private final Deque<S> waitlist;

	public LIFOWaitlist() {
		waitlist = new ArrayDeque<>();
	}

	public LIFOWaitlist(final Collection<? extends S> states) {
		waitlist = new ArrayDeque<>(states);
	}

	@Override
	public void add(final S state) {
		waitlist.push(checkNotNull(state));
	}

	@Override
	public boolean isEmpty() {
		return waitlist.isEmpty();
	}

	@Override
	public S remove() {
		return waitlist.pop();
	}

	@Override
	public void clear() {
		waitlist.clear();
	}
}
