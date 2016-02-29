package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface StopOperator<S extends State, P extends Precision> {

	public boolean stop(S state, Collection<S> reachedStates, P precision);
	
}
