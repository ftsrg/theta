package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

public interface SafetyChecker<S extends State, A extends Action, P extends Prec> {

	SafetyResult<S, A> check(final P prec);

}
