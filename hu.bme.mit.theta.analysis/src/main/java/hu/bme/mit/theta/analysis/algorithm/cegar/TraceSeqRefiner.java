package hu.bme.mit.theta.analysis.algorithm.cegar;

import java.util.List;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.Refutation;

public interface TraceSeqRefiner<S extends State, A extends Action, P extends Precision, R extends Refutation> {

	List<P> refine(Trace<S, A> trace, List<P> precisions, R refutation);

}
