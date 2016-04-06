package hu.bme.mit.inf.ttmc.formalism.tcfa;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Automaton;

public interface TCFA extends Automaton {

	@Override
	public TCFALoc getInitLoc();

	@Override
	public Collection<? extends TCFALoc> getLocs();

	@Override
	public Collection<? extends TCFAEdge> getEdges();

}