package hu.bme.mit.inf.ttmc.formalism.cfa;

import hu.bme.mit.inf.ttmc.formalism.common.Automaton;

public interface CFA extends Automaton<CFALoc, CFAEdge> {

	public CFALoc getFinalLoc();

	public CFALoc getErrorLoc();

}