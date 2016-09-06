package hu.bme.mit.inf.theta.analysis.algorithm.impl;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.analysis.State;
import hu.bme.mit.inf.theta.analysis.Trace;
import hu.bme.mit.inf.theta.analysis.algorithm.CounterexampleStatus;
import hu.bme.mit.inf.theta.analysis.refutation.Refutation;

public interface ConcretizerOp<S extends State, A extends Action, CS extends State, R extends Refutation> {

	CounterexampleStatus concretize(Trace<? extends S, A> counterexample);

	CounterexampleStatus getStatus();

	Trace<CS, A> getConcreteCounterexample();

	R getRefutation();
}
