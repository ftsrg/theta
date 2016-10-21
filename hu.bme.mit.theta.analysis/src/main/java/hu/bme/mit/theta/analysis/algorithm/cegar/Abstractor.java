package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public interface Abstractor<S extends State, A extends Action, P extends Precision> {

	ARG<S, A> init(final P precision);

	AbstractorStatus<S, A> check(ARG<S, A> arg, final P precision);

	default AbstractorStatus<S, A> initAndCheck(final P precision) {
		final ARG<S, A> arg = init(precision);
		final AbstractorStatus<S, A> status = check(arg, precision);
		return status;
	}
}
