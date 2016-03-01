package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface MutableReachedSet<S extends State> extends ReachedSet<S> {
	
	public void add(S state);	
	public void remove(S state);
	
	@Override
	public MutableWaitlist<S> getWaitlist();
	
}
