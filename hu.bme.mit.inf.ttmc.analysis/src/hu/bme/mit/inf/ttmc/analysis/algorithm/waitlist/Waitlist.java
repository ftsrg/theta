package hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface Waitlist<S extends State> {
	void add(S state);

	void addAll(Collection<? extends S> states);

	boolean isEmpty();

	S remove();

	void clear();
}
