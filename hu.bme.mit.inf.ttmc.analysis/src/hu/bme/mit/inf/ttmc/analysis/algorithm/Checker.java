package hu.bme.mit.inf.ttmc.analysis.algorithm;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.formalism.Formalism;

public interface Checker<F extends Formalism, S extends State, P extends Precision> {

	Optional<Counterexample<S>> check(P precision);

	Collection<S> getReachedSet();
}
