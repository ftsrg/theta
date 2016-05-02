package hu.bme.mit.inf.ttmc.formalism.ta;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Automaton;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;

public interface TA extends Automaton<TALoc, TAEdge> {

	public Collection<? extends Clock> getClocks();

}
