package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.automaton.Edge;

public interface AutomatonAbstraction<S extends State, P extends Precision, E extends Edge<?, E>> extends FormalismAbstraction<S, P> {

	public Collection<? extends S> getSuccStatesForEdge(S state, P precision, E edge);

}
