package hu.bme.mit.theta.analysis;

import java.util.Collection;

@FunctionalInterface
public interface TransferFunction<S extends State, A extends Action, P extends Precision> {

	Collection<? extends S> getSuccStates(S state, A action, P precision);

}