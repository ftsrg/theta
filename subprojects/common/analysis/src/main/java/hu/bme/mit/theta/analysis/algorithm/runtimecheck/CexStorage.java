package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.AbstractArg;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.ArgCexCheckHandler;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkState;

public class CexStorage<S extends State, A extends Action> {
	private final Map<Integer, Set<Integer>> counterexamples = new LinkedHashMap<>();
	private Integer currentArgHash = null;

	public <P extends Prec> void setCurrentArg(AbstractArg<S,A,P> arg) {
		currentArgHash = arg.hashCode();
	}

	public void addCounterexample(ArgTrace<S,A> cex) {
		checkState(currentArgHash!=null);
		if(ArgCexCheckHandler.instance.shouldCheck()) {
			int cexHashCode = cex.hashCode();
			if(counterexamples.containsKey(currentArgHash)) {
				counterexamples.get(currentArgHash).add(cexHashCode);
			} else {
				LinkedHashSet<Integer> cexHashCodes = new LinkedHashSet<>();
				cexHashCodes.add(cexHashCode);
				counterexamples.put(currentArgHash, cexHashCodes);
			}
		}
	}

	public boolean checkIfCounterexampleNew(ArgTrace<S,A> cex) {
		checkState(currentArgHash!=null);
		if(ArgCexCheckHandler.instance.shouldCheck()) {
			int cexHashCode = cex.hashCode();
			if (counterexamples.containsKey(currentArgHash)) {
				if (counterexamples.get(currentArgHash).contains(cexHashCode)) {
					System.err.println("Counterexample WAS present before");
					return false;
				}
			}

			System.err.println("Counterexample was NOT present before");
			return true;
		} else {
			return true;
		}
	}

	public <P extends Prec> boolean checkIfArgNew(AbstractArg<S,A,P> arg) {
		return counterexamples.containsKey(arg.hashCode());
	}
}
