package hu.bme.mit.inf.ttmc.analysis.algorithm.old;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface Counterexample<S extends State> extends Iterable<S> {
	int size();

	S get(int i);
}
