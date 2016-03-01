package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Analysis;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.MergeOperator;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.StopOperator;
import hu.bme.mit.inf.ttmc.analysis.TransferRelation;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Algorithm;
import hu.bme.mit.inf.ttmc.analysis.algorithm.MutableReachedSet;
import hu.bme.mit.inf.ttmc.analysis.algorithm.MutableWaitlist;
import hu.bme.mit.inf.ttmc.analysis.algorithm.ReachedSet;

public class CPAAlgorithm<S extends State> implements Algorithm<S> {

	final Domain<S> domain;
	final TransferRelation<S> transferRelation;
	final MergeOperator<S> mergeOperator;
	final StopOperator<S> stopOperator;
	
	public CPAAlgorithm(final Analysis<S> analysis) {
		domain = analysis.getDomain();
		transferRelation = analysis.getTransferRelation();
		mergeOperator = analysis.getMergeOperator();
		stopOperator = analysis.getStopOperator();
	}
	
	@Override
	public ReachedSet<S> run(final MutableReachedSet<S> reachedSet) {
		final MutableWaitlist<S> waitlist = reachedSet.getWaitlist();

		while (!waitlist.isEmpty()) {
			final S state = waitlist.pop();
			
			final Collection<S> succStates = transferRelation.getSuccessors(state);
			
			for (S succState : succStates) {
				
				for (S reachedState : reachedSet) {
					final S mergedState = mergeOperator.merge(succState, reachedState);
					
					if (!mergedState.equals(reachedState)) {
						reachedSet.add(mergedState);
						reachedSet.remove(reachedState);
					}
				}
				
				final boolean stop = stopOperator.stop(succState, reachedSet.asCollection());
				if (!stop) {
					reachedSet.add(succState);
				}
			}
		}
		
		return reachedSet;
	}

}
