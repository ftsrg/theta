package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

public interface InitStates<S extends State<S>> {
	public Collection<? extends S> get();
}
