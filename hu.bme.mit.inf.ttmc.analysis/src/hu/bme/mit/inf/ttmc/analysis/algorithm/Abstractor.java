package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.impl.ARG;

public interface Abstractor<S extends State, A extends Action, P extends Precision> {

	void init(final P precision);

	void check(final P precision);

	ARG<S, A> getARG();

	AbstractorStatus getStatus();

}
