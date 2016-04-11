package hu.bme.mit.inf.ttmc.analysis.algorithm;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.State;

public interface Algorithm<S extends State<S>> {

	public Collection<S> run(final Collection<? extends S> reachedSet);

}
