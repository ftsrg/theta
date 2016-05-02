package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Edge;

public interface AutomatonTransferRelation<S extends State, P extends Precision, E extends Edge<?, E>>
		extends TransferRelation<S, P> {

	public Collection<? extends S> getSuccStatesForEdge(S state, P precision, E edge);

}
