package hu.bme.mit.inf.ttmc.analysis;

import java.util.List;

// TODO: find a good interface for alternating S,A,S,...,S,A,S sequence
public interface Counterexample<S extends State, A extends Action> {

	int size();

	S getState(int i);

	List<S> getStates();

	A getAction(int i);

	List<A> getActions();
}
