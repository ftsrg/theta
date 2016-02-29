package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface MutableReachedSet<S extends State, P extends Precision> extends ReachedSet<S, P> {
	
	public void add(S state, P precision);	
	public void remove(S state);
	
	@Override
	public MutableWaitlist<S> getWaitlist();
	
}
