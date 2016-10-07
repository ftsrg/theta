package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public interface CegarLoop<P extends Precision, CS extends State, A extends Action> {

	CegarStatus check(final P initPrecision);

	CegarStatus getStatus();

	Trace<CS, A> getCex();
}
