package hu.bme.mit.theta.formalism.common;

import java.util.Collection;

public interface Automaton<L extends Loc<L, E>, E extends Edge<L, E>> {

	L getInitLoc();

	Collection<? extends L> getLocs();

	Collection<? extends E> getEdges();

}
