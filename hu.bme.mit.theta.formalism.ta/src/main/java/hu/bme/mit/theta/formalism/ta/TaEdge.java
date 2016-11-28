package hu.bme.mit.theta.formalism.ta;

import java.util.Collection;

import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;

public interface TaEdge extends Edge<TaLoc, TaEdge> {

	ClockConstr getGuard();

	Collection<? extends ClockDecl> getResets();
}
