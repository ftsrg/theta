package hu.bme.mit.inf.ttmc.analysis;

import java.util.Collection;

@FunctionalInterface
public interface TransferFunction<S extends State, P extends Precision, Trans> {

	Collection<S> getSuccStates(S state, P precision, Trans trans);

}