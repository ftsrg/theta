package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.refutation.Refutation;

public interface RefinerOp<S extends State, A extends Action, R extends Refutation, P extends Precision> {

	P refine(P precision, R refutation, Counterexample<S, A> counterexample);
}
