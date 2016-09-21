package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public interface ConcretizerOp<S extends State, A extends Action, CS extends State, R extends Refutation> {

	CounterexampleStatus concretize(Trace<? extends S, A> counterexample);

	CounterexampleStatus getStatus();

	Trace<CS, A> getConcreteCounterexample();

	R getRefutation();
}
