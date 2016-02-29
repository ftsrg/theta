package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface ReachedSet<S extends State, P extends Precision> extends Iterable<S> {

	public boolean contains(S state);
	public boolean isEmpty();
	public int size();
	
	public P getPrecision(S state);
	public Waitlist<S> getWaitlist();
}