package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Edge;

public interface AutomatonTransferRelation<S extends State, E extends Edge<?, E>> extends TransferRelation<S> {

	public Collection<? extends S> getSuccStatesForEdge(S state, E edge);

}
