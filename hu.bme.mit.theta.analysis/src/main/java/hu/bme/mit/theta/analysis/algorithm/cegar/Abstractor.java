package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

public interface Abstractor<S extends State, A extends Action, P extends Precision> {

	void init(final P precision);

	AbstractorStatus<S, A> check(final P precision);
}
