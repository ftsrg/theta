package hu.bme.mit.inf.theta.analysis;

import java.util.Collection;

@FunctionalInterface
public interface InitFunction<S extends State, P extends Precision> {

	Collection<? extends S> getInitStates(P precision);

}
