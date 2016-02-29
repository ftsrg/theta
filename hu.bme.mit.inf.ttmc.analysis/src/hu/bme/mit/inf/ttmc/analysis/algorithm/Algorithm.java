package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface Algorithm<S extends State, P extends Precision> {
	
	public AlgorithmStatus run(final MutableReachedSet<S, P> reachedSet);
	
}
