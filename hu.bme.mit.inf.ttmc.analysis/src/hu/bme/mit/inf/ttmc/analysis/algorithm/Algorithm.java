package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface Algorithm<S extends State> {
	
	public ReachedSet<S> run(final MutableReachedSet<S> reachedSet);
	
}
