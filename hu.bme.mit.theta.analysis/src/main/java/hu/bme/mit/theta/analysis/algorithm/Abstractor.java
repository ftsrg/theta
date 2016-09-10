package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.impl.ARG;

public interface Abstractor<S extends State, A extends Action, P extends Precision> {

	void init(final P precision);

	void check(final P precision);

	ARG<S, A, P> getARG();

	AbstractorStatus getStatus();

}
