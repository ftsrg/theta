package hu.bme.mit.theta.analysis;

import java.util.Collection;

public interface ActionFunction<S extends State, A extends Action> {

	public Collection<? extends A> getEnabledActionsFor(S state);

}
