package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.Refutation;

public interface ConcretizerOp<S extends State, A extends Action, R extends Refutation> {

	CexStatus<R> checkConcretizable(Trace<? extends S, A> cex);

}
