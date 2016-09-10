package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public interface CEGARLoop<P extends Precision, CS extends State, A extends Action> {

	CEGARStatus check(final P initPrecision);

	CEGARStatus getStatus();

	Trace<CS, A> getCounterexample();
}
