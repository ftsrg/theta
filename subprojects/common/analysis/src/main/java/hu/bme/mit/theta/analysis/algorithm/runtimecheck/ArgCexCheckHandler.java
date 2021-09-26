package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;

public class ArgCexCheckHandler<S extends State, A extends Action> {
	public static ArgCexCheckHandler instance = new ArgCexCheckHandler();
	private CexStorage<S,A> cexStorage;

	public void setArgCexCheck(boolean shouldCheck, boolean multiseq) {
		if(shouldCheck) {
			if(multiseq) {
				cexStorage = new MultiCexStorage<S,A>();
			} else {
				cexStorage = new SingleCexStorage<S,A>();
			}
		} else {
			cexStorage = null;
		}
	}

	public boolean checkIfCounterexampleNew(ArgTrace<S,A> cex) {
		if(cexStorage!=null) {
			return cexStorage.checkIfCounterexampleNew(cex);
		} else return true;
	}

	public <P extends Prec> void setCurrentArg(AbstractArg<S,A,P> arg) {
		if(cexStorage != null) {
			cexStorage.setCurrentArg(arg);
		}
	}

	public <P extends Prec> void checkAndStop(ARG<S,A> arg, P prec) {
		if(cexStorage!=null && cexStorage.check(arg,prec)) {
			throw new NotSolvableException();
		}
	}

	public void addCounterexample(ArgTrace<S,A> cexToConcretize) {
		if(cexStorage!=null) {
			cexStorage.addCounterexample(cexToConcretize);
		}
	}
}
