package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

abstract class CexStorage<S extends State, A extends Action> {
	abstract <P extends Prec> void setCurrentArg(AbstractArg<S,A,P> arg);

	abstract void addCounterexample(ArgTrace<S,A> cex);

	abstract <P extends Prec> boolean check(ARG<S,A> arg, P prec);

	abstract boolean checkIfCounterexampleNew(ArgTrace<S,A> cex);
}
