package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;

public interface TransferRelation<S extends AbstractState> {

	public Collection<S> getSuccessors(S state);
	public Collection<S> getSuccessors(S state, CFAEdge edge);
	
}
