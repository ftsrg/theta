package hu.bme.mit.inf.theta.analysis.algorithm;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.analysis.Precision;
import hu.bme.mit.inf.theta.analysis.State;
import hu.bme.mit.inf.theta.analysis.Trace;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.ARG;

public interface Refiner<S extends State, A extends Action, P extends Precision, CS extends State> {

	void refine(ARG<S, A, ? super P> arg, P precision);

	CounterexampleStatus getStatus();

	Trace<CS, A> getConcreteCounterexample();

	P getRefinedPrecision();
}
