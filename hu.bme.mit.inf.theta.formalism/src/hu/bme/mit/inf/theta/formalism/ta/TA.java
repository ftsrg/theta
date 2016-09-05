package hu.bme.mit.inf.theta.formalism.ta;

import java.util.Collection;

import hu.bme.mit.inf.theta.formalism.common.automaton.Automaton;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;

public interface TA extends Automaton<TaLoc, TaEdge> {

	public Collection<? extends ClockDecl> getClocks();

}
