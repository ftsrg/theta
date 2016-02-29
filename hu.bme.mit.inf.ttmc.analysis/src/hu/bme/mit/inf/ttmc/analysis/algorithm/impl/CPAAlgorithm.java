package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.MergeOperator;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.RefinementOperator;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;
import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;
import hu.bme.mit.inf.ttmc.analysis.algorithm.AlgorithmStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.MutableReachedSet;
import hu.bme.mit.inf.ttmc.analysis.algorithm.MutableWaitlist;

public class CPAAlgorithm<S extends State, P extends Precision> implements Algorithm<S, P> {

	final Domain<S> domain;
	final TransferRelation<S, P> transferRelation;
	final MergeOperator<S, P> mergeOperator;
	final StopOperator<S, P> stopOperator;
	final RefinementOperator<S, P> refinementOperator;
	
	public CPAAlgorithm(final Analysis<S, P> analysis) {
		domain = analysis.getDomain();
		transferRelation = analysis.getTransferRelation();
		mergeOperator = analysis.getMergeOperator();
		stopOperator = analysis.getStopOperator();
		refinementOperator = analysis.getRefinementOperator();
	}
	
	@Override
	public AlgorithmStatus run(MutableReachedSet<S, P> reachedSet) {
		final MutableWaitlist<S> waitlist = reachedSet.getWaitlist();
		
		while (!waitlist.isEmpty()) {
			final S state = waitlist.pop();
			
			// TODO
			final P precision = null;
			
			final Collection<S> succStates = transferRelation.getSuccessors(state, precision);
			
			for (S succState : succStates) {
				final P succPrecision = reachedSet.getPrecision(succState);
				
				for (S reachedState : reachedSet) {
					final S mergedState = mergeOperator.merge(succState, reachedState, succPrecision);
					
					if (!mergedState.equals(reachedState)) {
						reachedSet.add(mergedState, succPrecision);
						reachedSet.remove(reachedState);
					}
				}
				
				final boolean stop = stopOperator.stop(succState, reachedSet.asCollection(), succPrecision);
				if (!stop) {
					reachedSet.add(succState, succPrecision);
				}
			}
			
		}
		
		// TODO
		return null;
	}

}
