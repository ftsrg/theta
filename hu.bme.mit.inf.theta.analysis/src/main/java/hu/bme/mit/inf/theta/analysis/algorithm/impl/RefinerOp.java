package hu.bme.mit.inf.theta.analysis.algorithm.impl;

import hu.bme.mit.inf.theta.analysis.Action;
import hu.bme.mit.inf.theta.analysis.Precision;
import hu.bme.mit.inf.theta.analysis.State;
import hu.bme.mit.inf.theta.analysis.Trace;
import hu.bme.mit.inf.theta.analysis.refutation.Refutation;

public interface RefinerOp<S extends State, A extends Action, R extends Refutation, P extends Precision> {

	P refine(P precision, R refutation, Trace<S, A> counterexample);
}
