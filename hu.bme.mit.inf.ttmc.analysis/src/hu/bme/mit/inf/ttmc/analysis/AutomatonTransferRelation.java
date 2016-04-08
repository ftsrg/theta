package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Edge;

public interface AutomatonTransferRelation<S extends State<S>, E extends Edge> extends TransferRelation<S> {

	public Collection<S> getSuccStatesForEdge(S state, E edge);

}
