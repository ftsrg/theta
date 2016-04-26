package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface InitStates<S extends State> {
	public Collection<? extends S> get();
}
