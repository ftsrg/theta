package hu.bme.mit.inf.ttmc.formalism.common.automaton;

import java.util.Collection;

public interface Automaton<L extends Loc<L, E>, E extends Edge<L, E>> {

	public L getInitLoc();

	public Collection<? extends L> getLocs();

	public Collection<? extends E> getEdges();

}
