package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public interface RefinerOp<S extends State, A extends Action, R extends Refutation, P extends Precision> {

	P refine(P precision, R refutation, Trace<S, A> counterexample);
}
