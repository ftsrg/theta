package hu.bme.mit.inf.ttmc.formalism.ta;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Automaton;

public interface TA extends Automaton {

	@Override
	public TALoc getInitLoc();

	@Override
	public Collection<? extends TALoc> getLocs();

	@Override
	public Collection<? extends TAEdge> getEdges();

}
