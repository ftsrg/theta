package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface StopOperator<S extends State<S>> {

	public boolean stop(S state, Collection<S> reachedStates);

}
