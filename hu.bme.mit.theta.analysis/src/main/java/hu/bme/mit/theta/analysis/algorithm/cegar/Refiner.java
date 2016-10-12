package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public interface Refiner<S extends State, A extends Action, P extends Precision> {

	void refine(ARG<S, A> arg, P precision);

	CexStatus getStatus();

	Trace<S, A> getCex();

	P getRefinedPrecision();
}
