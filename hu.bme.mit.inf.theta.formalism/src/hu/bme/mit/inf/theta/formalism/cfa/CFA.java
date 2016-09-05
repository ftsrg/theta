package hu.bme.mit.inf.theta.formalism.cfa;

import hu.bme.mit.inf.theta.formalism.common.automaton.Automaton;

public interface CFA extends Automaton<CfaLoc, CfaEdge> {

	public CfaLoc getFinalLoc();

	public CfaLoc getErrorLoc();

}