package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

public interface Refiner<S extends State, A extends Action, P extends Precision> {

	RefinerStatus<S, A, P> refine(AbstractionState<S, A, P> abstractionState);
}
