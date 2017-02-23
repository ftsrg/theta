package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public interface Refiner<S extends State, A extends Action, P extends Prec> {

	RefinerResult<S, A, P> refine(ARG<S, A> arg, P precision);
}
