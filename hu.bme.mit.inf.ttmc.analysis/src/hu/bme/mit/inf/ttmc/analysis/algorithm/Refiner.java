package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;

public interface Refiner<S extends State, A extends Action, P extends Precision> {

	CounterexampleStatus checkAndRefine(ARG<S, A> arg);

	CounterexampleStatus getStatus();

	Counterexample<ExplState> getConcreteCounterexample();

	P getRefinedPrecision();

}
