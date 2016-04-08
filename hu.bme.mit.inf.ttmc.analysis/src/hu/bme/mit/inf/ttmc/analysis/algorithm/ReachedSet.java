package hu.bme.mit.inf.ttmc.analysis.algorithm;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface ReachedSet<S extends State<S>> extends Iterable<S> {

	public boolean contains(S state);

	public boolean isEmpty();

	public int size();

	public Collection<S> asCollection();

	public Waitlist<S> getWaitlist();
}