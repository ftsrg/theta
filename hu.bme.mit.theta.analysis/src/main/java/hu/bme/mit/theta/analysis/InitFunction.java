package hu.bme.mit.theta.analysis;

import java.util.Collection;

@FunctionalInterface
public interface InitFunction<S extends State, P extends Prec> {

	Collection<? extends S> getInitStates(P prec);

}
