package hu.bme.mit.inf.ttmc.formalism.ta;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.formalism.common.Edge;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Constr;

public interface TAEdge extends Edge<TALoc, TAEdge> {

	public Constr getGuard();

	public Collection<? extends Clock> getResets();
}
