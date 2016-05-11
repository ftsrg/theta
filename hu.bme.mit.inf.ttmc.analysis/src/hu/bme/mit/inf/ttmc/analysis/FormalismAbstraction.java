package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface FormalismAbstraction<S extends State, P extends Precision> {

	public Collection<? extends S> getStartStates(P precision);

	public Collection<? extends S> getSuccStates(S state, P precision);

	public boolean isTarget(S state);
}
