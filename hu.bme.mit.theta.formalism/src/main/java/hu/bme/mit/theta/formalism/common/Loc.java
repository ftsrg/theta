package hu.bme.mit.theta.formalism.common;

import java.util.Collection;

public interface Loc<L extends Loc<L, E>, E extends Edge<L, E>> {

	Collection<? extends E> getInEdges();

	Collection<? extends E> getOutEdges();

}
