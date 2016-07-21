package hu.bme.mit.inf.ttmc.analysis;

import java.util.List;

// TODO: find a good interface for alternating S,A,S,...,S,A,S sequence
public interface Trace<S extends State, A extends Action> {

	int length();

	S getState(int i);

	A getAction(int i);

	List<S> getStates();

	List<A> getActions();

}
