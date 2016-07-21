package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Trace;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.ARG;

public interface Refiner<S extends State, A extends Action, P extends Precision, CS extends State> {

	void refine(ARG<S, A> arg, P precision);

	CounterexampleStatus getStatus();

	Trace<CS, A> getConcreteCounterexample();

	P getRefinedPrecision();
}
