package hu.bme.mit.theta.formalism.ta;

import java.util.Collection;

import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.decl.ClockDecl;

public interface TaEdge extends Edge<TaLoc, TaEdge> {

	ClockConstr getGuard();

	Collection<? extends ClockDecl> getResets();
}
