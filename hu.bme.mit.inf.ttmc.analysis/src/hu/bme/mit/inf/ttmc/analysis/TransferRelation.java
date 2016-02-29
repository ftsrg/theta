package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.program.cfa.CFAEdge;

public interface TransferRelation<S extends State, P extends Precision> {

	public Collection<S> getSuccessors(S state, P precision);
	public Collection<S> getSuccessors(S state, P precision, CFAEdge edge);
	
}
