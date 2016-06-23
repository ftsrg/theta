package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

@FunctionalInterface
public interface InitFunction<S extends State, P extends Precision> {

	Collection<? extends S> getInitStates(P precision);

}
