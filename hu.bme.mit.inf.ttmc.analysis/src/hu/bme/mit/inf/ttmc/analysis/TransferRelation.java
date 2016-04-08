package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface TransferRelation<S extends State<S>> {

	public Collection<S> getSuccStates(S state);

}
