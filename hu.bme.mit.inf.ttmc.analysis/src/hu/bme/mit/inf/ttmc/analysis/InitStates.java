package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface InitStates<S extends State, P extends Precision> {

	public Collection<? extends S> get(P precision);

}
