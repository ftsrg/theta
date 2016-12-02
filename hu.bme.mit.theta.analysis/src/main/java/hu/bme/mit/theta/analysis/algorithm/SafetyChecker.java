package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

public interface SafetyChecker<S extends State, A extends Action, P extends Precision> {

	SafetyStatus<S, A> check(final P precision);

}
