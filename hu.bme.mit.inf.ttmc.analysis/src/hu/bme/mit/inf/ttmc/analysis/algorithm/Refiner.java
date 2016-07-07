package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.ARG;

public interface Refiner<S extends State, A extends Action, P extends Precision, CS extends State> {

	RefinerStatus refine(ARG<S, A> arg);

	RefinerStatus getStatus();

	Counterexample<CS, A> getConcreteCounterexample();

	P getRefinedPrecision();
}
