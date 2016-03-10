package hu.bme.mit.inf.ttmc.formalism.cfa;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Automaton;

public interface CFA extends Automaton {

	@Override
	public CFALoc getInitLoc();

	public CFALoc getFinalLoc();

	public CFALoc getErrorLoc();

	@Override
	public Collection<? extends CFALoc> getLocs();

	@Override
	public Collection<? extends CFAEdge> getEdges();

}