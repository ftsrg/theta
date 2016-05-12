package hu.bme.mit.inf.ttmc.analysis;

public interface ErrorStates<S extends State> {

	public boolean isError(S state);
}
