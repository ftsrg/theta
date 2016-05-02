package hu.bme.mit.inf.ttmc.formalism.common.automaton;

import java.util.Collection;

public interface Loc<L extends Loc<L, E>, E extends Edge<L, E>> {

	public Collection<? extends E> getInEdges();

	public Collection<? extends E> getOutEdges();

}
