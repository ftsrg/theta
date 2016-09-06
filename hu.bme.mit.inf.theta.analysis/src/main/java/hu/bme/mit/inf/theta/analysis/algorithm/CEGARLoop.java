package hu.bme.mit.inf.theta.analysis.algorithm;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.analysis.Precision;
import hu.bme.mit.inf.theta.analysis.State;
import hu.bme.mit.inf.theta.analysis.Trace;

public interface CEGARLoop<P extends Precision, CS extends State, A extends Action> {

	CEGARStatus check(final P initPrecision);

	CEGARStatus getStatus();

	Trace<CS, A> getCounterexample();
}
