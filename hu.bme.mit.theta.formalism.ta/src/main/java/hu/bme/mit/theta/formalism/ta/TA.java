package hu.bme.mit.theta.formalism.ta;

import java.util.Collection;

import hu.bme.mit.theta.formalism.common.Automaton;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;

public interface TA extends Automaton<TaLoc, TaEdge> {

	Collection<? extends ClockDecl> getClocks();

}
