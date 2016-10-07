package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public interface ConcretizerOp<S extends State, A extends Action, CS extends State, R extends Refutation> {

	CexStatus concretize(Trace<? extends S, A> cex);

	CexStatus getStatus();

	Trace<CS, A> getConcreteCex();

	R getRefutation();
}
