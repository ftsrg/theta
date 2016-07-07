package hu.bme.mit.inf.ttmc.analysis;

// TODO: find a good interface for alternating S,A,S,...,S,A,S sequence
public interface Counterexample<S extends State, A extends Action> {

	int size();

	S getState(int i);

	A getAction(int i);
}
