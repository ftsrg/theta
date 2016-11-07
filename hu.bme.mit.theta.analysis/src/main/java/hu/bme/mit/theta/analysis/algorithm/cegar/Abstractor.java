package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

public interface Abstractor<S extends State, A extends Action, P extends Precision> {

	AbstractionState<S, A, P> init(final P precision);

	AbstractorStatus<S, A, P> check(AbstractionState<S, A, P> abstractionState);

	default AbstractorStatus<S, A, P> initAndCheck(final P precision) {
		final AbstractionState<S, A, P> init = init(precision);
		final AbstractorStatus<S, A, P> status = check(init);
		return status;
	}
}
