package hu.bme.mit.inf.theta.formalism.ta;

import java.util.Collection;

import hu.bme.mit.inf.theta.formalism.common.automaton.Edge;
import hu.bme.mit.inf.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.theta.formalism.ta.constr.ClockConstr;

public interface TaEdge extends Edge<TaLoc, TaEdge> {

	public ClockConstr getGuard();

	public Collection<? extends ClockDecl> getResets();
}
