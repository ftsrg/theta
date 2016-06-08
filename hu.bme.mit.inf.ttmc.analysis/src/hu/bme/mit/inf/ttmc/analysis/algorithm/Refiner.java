package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.refutation.Refutation;

public interface Refiner<S extends State, P extends Precision, R extends Refutation> {

	P refine(P precision, Counterexample<S> abstractCex, R refutation);
}
