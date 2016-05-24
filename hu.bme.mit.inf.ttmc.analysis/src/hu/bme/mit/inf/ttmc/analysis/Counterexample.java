package hu.bme.mit.inf.ttmc.analysis;

public interface Counterexample<S extends State> extends Iterable<S> {
	int size();

	S get(int i);
}
