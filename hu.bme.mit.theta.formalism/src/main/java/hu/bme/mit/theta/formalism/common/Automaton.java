package hu.bme.mit.theta.formalism.common;

import java.util.Collection;

import hu.bme.mit.theta.formalism.Formalism;

public interface Automaton<L extends Loc<L, E>, E extends Edge<L, E>> extends Formalism {

	public L getInitLoc();

	public Collection<? extends L> getLocs();

	public Collection<? extends E> getEdges();

}
