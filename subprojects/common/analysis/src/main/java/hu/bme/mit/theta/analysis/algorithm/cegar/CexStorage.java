package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.runtimecheck.AbstractArg;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

public class CexStorage<S extends State, A extends Action> {
	private final Map<Integer, Set<Integer>> counterexamples = new LinkedHashMap<>();
	private Integer currentArgHash = null;

	// TODO any other calls of this needed outside the abstractor?
	public void setCurrentArg(AbstractArg arg) {
		currentArgHash = arg.hashCode();
	}

	public void addCounterexample(ArgTrace<S,A> cex) {
		checkState(currentArgHash!=null);
//		if(active) {
			int cexHashCode = cex.hashCode();
			if(counterexamples.containsKey(currentArgHash)) {
				counterexamples.get(currentArgHash).add(cexHashCode);
			} else {
				counterexamples.put(currentArgHash, new LinkedHashSet<>(cexHashCode));
			}
//		}
	}

	public boolean checkIfCounterexampleNew(ArgTrace<S,A> cex) {
		checkState(currentArgHash!=null);
//		if(active) {
			int cexHashCode = cex.hashCode();
			if (counterexamples.containsKey(currentArgHash)) {
				if (counterexamples.get(currentArgHash).contains(cexHashCode)) {
					System.err.println("Counterexample WAS present before");
					return false;
				}
			}

			System.err.println("Counterexample was NOT present before");
			return true;
//		} else {
//			return true;
//		}
	}
}
