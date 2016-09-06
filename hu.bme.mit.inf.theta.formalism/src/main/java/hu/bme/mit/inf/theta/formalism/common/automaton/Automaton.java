package hu.bme.mit.inf.theta.formalism.common.automaton;

import java.util.Collection;

import hu.bme.mit.inf.theta.formalism.Formalism;

public interface Automaton<L extends Loc<L, E>, E extends Edge<L, E>> extends Formalism {

	public L getInitLoc();

	public Collection<? extends L> getLocs();

	public Collection<? extends E> getEdges();

}
