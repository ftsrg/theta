package hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Queue;

import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist.Waitlist;

public class FIFOWaitlist<S extends State> implements Waitlist<S> {

	private final Queue<S> waitlist;

	public FIFOWaitlist() {
		waitlist = new ArrayDeque<>();
	}

	public FIFOWaitlist(final Collection<? extends S> states) {
		waitlist = new ArrayDeque<>(states);
	}

	@Override
	public void add(final S state) {
		waitlist.add(checkNotNull(state));
	}

	@Override
	public boolean isEmpty() {
		return waitlist.isEmpty();
	}

	@Override
	public S remove() {
		return waitlist.remove();
	}

	@Override
	public void clear() {
		waitlist.clear();
	}

}
