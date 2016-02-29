package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface Waitlist<S extends State> {
	
	public S peek();
	
	public boolean isEmpty();
	public int size();
	
}
