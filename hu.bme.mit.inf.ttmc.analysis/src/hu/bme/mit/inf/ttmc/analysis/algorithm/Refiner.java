package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.Refutation;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface Refiner<S extends State, P extends Precision, R extends Refutation> {

	P refine(P precision, R refutation);
}
