package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

@FunctionalInterface
public interface TransferFunction<S extends State, P extends Precision> {

	Collection<? extends S> getSuccStates(S state, P precision);

}