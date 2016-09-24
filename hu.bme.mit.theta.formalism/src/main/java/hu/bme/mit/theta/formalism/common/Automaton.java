package hu.bme.mit.theta.formalism.common;

import java.util.Collection;

public interface Automaton<L extends Loc<L, E>, E extends Edge<L, E>> {

	public L getInitLoc();

	public Collection<? extends L> getLocs();

	public Collection<? extends E> getEdges();

}
