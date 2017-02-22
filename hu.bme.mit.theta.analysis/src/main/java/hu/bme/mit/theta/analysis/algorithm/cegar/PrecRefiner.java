package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.Refutation;

public interface PrecRefiner<S extends State, A extends Action, P extends Precision, R extends Refutation> {

	P refine(Trace<S, A> trace, P precision, R refutation);

}
