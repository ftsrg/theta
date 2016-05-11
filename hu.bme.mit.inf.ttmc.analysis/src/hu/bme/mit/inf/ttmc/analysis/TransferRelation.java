package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface TransferRelation<S extends State, P extends Precision> {

	public Collection<? extends S> getSuccStates(S state, P precision);

}
