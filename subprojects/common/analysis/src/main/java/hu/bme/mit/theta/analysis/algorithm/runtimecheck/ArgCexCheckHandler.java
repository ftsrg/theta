package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

public class ArgCexCheckHandler<S extends State, A extends Action> {
	public static ArgCexCheckHandler instance = new ArgCexCheckHandler();
	private AbstractArgStorage<S,A> abstractArgStorage;

	public void setArgCexCheck(boolean shouldCheck, boolean multiseq) {
		if(shouldCheck) {
			if(multiseq) {
				abstractArgStorage = new MultiCexAbstractArgStorage<S,A>();
			} else {
				abstractArgStorage = new SingleCexAbstractArgStorage<S,A>();
			}
		} else {
			abstractArgStorage = null;
		}
	}

	public boolean checkIfCounterexampleNew(ArgTrace<S,A> cex) {
		if(abstractArgStorage !=null) {
			return abstractArgStorage.checkIfCounterexampleNew(cex);
		} else return true;
	}

	public <P extends Prec> void setCurrentArg(AbstractArg<S,A,P> arg) {
		if(abstractArgStorage != null) {
			abstractArgStorage.setCurrentArg(arg);
		}
	}

	public <P extends Prec> void checkAndStop(ARG<S,A> arg, P prec) {
		if(abstractArgStorage !=null && abstractArgStorage.check(arg,prec)) {
			throw new NotSolvableException();
		}
	}

	public void addCounterexample(ArgTrace<S,A> cexToConcretize) {
		if(abstractArgStorage !=null) {
			abstractArgStorage.addCounterexample(cexToConcretize);
		}
	}
}
