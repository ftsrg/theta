package hu.bme.mit.inf.ttmc.formalism.ta;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.automaton.Edge;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;

public interface TAEdge extends Edge<TALoc, TAEdge> {

	public ClockConstr getGuard();

	public Collection<? extends ClockDecl> getResets();
}
