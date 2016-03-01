package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface StopOperator<S extends State> {

	public boolean stop(S state, Collection<S> reachedStates);
	
}
