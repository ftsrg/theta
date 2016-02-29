package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;
import hu.bme.mit.inf.ttmc.analysis.algorithm.AlgorithmStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.MutableReachedSet;

public class CPAAlgorithm<S extends State, P extends Precision> implements Algorithm<S, P> {

	public CPAAlgorithm(final Analysis<S, P> analysis) {
		
	}
	
	
	
	@Override
	public AlgorithmStatus run(MutableReachedSet<S, P> reachedSet) {
		
		
		
		return null;
	}

}
