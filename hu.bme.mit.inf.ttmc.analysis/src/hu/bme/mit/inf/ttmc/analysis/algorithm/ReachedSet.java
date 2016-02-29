package hu.bme.mit.inf.ttmc.analysis.algorithm;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface ReachedSet<S extends State, P extends Precision> extends Iterable<S> {

	public boolean contains(S state);
	public boolean isEmpty();
	public int size();
	
	public Collection<S> asCollection();
	
	public P getPrecision(S state);
	public Waitlist<S> getWaitlist();
}