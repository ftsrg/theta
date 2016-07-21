package hu.bme.mit.inf.ttmc.analysis.algorithm;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Trace;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;

public interface CEGARLoop<P extends Precision, CS extends State, A extends Action> {

	CEGARStatus check(final P initPrecision);

	CEGARStatus getStatus();

	Trace<CS, A> getCounterexample();
}
