package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.cegar.CexStorage;

import java.util.stream.Stream;

public class ArgCexCheckHandler {
	public static ArgCexCheckHandler instance = new ArgCexCheckHandler();
	private boolean shouldCheck = false;
	private boolean multiseq = false;

	public void setArgCexCheck(boolean shouldThrow, boolean multiseq) {
		this.multiseq = multiseq;
		this.shouldCheck = shouldThrow;
	}

	public boolean shouldCheck() {
		return shouldCheck;
	}

	public <S extends State, A extends Action, P extends Prec> void checkAndStop(ARG<S,A> arg, P prec, CexStorage<S,A> cexStorage) {
		if(shouldCheck) {
			if(multiseq && cexStorage.checkIfArgNew(new AbstractArg<>(arg, prec))) {
				// TODO it would be better to create a "multiseq check storage" in this case so we only store the ARGs, as the cexs are superfluous in this case
				System.err.println("Not solvable!");
				throw new NotSolvableException();
			} else if(arg.getCexs().noneMatch(cexStorage::checkIfCounterexampleNew)) {
				System.err.println("Not solvable!");
				throw new NotSolvableException();
			}
		}
	}
}
