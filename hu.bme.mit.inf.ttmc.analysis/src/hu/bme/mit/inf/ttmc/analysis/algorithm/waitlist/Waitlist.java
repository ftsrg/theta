package hu.bme.mit.inf.ttmc.analysis.algorithm.waitlist;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface Waitlist<S extends State> {
	void add(S state);

	boolean isEmpty();

	S remove();

	void clear();
}
