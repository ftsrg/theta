package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CounterexampleStatus;
import hu.bme.mit.inf.ttmc.analysis.refutation.Refutation;

public interface ConcretizerOperator<S extends State, A extends Action, CS extends State, R extends Refutation> {

	CounterexampleStatus concretize(Counterexample<? extends S, A> counterexample);

	CounterexampleStatus getStatus();

	Counterexample<CS, A> getConcreteCounterexample();

	R getRefutation();
}
