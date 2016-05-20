package hu.bme.mit.inf.ttmc.analysis.algorithm;

import java.util.Optional;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface Checker<S extends State, P extends Precision> {

	public Optional<Counterexample<S>> check(P precision);
}
