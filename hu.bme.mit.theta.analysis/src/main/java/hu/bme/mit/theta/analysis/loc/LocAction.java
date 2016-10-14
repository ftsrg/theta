package hu.bme.mit.theta.analysis.loc;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

public interface LocAction<L extends Loc<L, E>, E extends Edge<L, E>> extends Action {

	public E getEdge();

}
