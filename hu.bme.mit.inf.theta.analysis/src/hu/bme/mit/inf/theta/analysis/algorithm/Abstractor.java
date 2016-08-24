package hu.bme.mit.inf.theta.analysis.algorithm;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.analysis.Precision;
import hu.bme.mit.inf.theta.analysis.State;
import hu.bme.mit.inf.theta.analysis.algorithm.impl.ARG;

public interface Abstractor<S extends State, A extends Action, P extends Precision> {

	void init(final P precision);

	void check(final P precision);

	ARG<S, A, P> getARG();

	AbstractorStatus getStatus();

}
