package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

/**
 * Used by the {@link ArgCexCheckHandler} to store and check abstract ARGs and Counterexamples and if there is any refinement progress on them
 * The concrete implemented ARG storages might differ in what configurations they support (e.g. refinement methods)
 * @param <S>
 * @param <A>
 */
abstract class AbstractArgStorage<S extends State, A extends Action> {
	abstract <P extends Prec> void setCurrentArg(AbstractArg<S,A,P> arg);

	abstract void addCounterexample(ArgTrace<S,A> cex);

	abstract <P extends Prec> boolean check(ARG<S,A> arg, P prec);

	abstract boolean checkIfCounterexampleNew(ArgTrace<S,A> cex);
}
