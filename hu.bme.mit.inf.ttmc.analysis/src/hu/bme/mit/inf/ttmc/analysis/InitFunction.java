package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

@FunctionalInterface
public interface InitFunction<S extends State, P extends Precision, Init> {

	Collection<S> getInitStates(P precision, Init init);

}
