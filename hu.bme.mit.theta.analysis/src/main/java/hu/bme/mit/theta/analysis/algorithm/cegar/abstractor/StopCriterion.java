package hu.bme.mit.theta.analysis.algorithm.cegar.abstractor;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public interface StopCriterion<S extends State, A extends Action> {
	boolean canStop(ARG<S, A> arg);
}
