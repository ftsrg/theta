package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

import java.util.LinkedHashSet;
import java.util.Set;

public class CexStorage<S extends State, A extends Action> {
	private Set<Integer> counterexamples = new LinkedHashSet<>();
	private ArgTrace<S,A> firstCexInIteration = null;
	private boolean active = false;

	public void stop() {
		active = false;
	}

	public void start() {
		counterexamples.clear();
		active = true;
	}

	public void addCounterexample(ArgTrace<S,A> cex) {
		if(active) {
			counterexamples.add(cex.hashCode());
		}
	}

	public boolean checkIfCounterexampleNew(ArgTrace<S,A> cex) {
		if(active) {
			if(counterexamples.contains(cex.hashCode())) {
				System.err.println("Counterexample WAS present before");
				return false;
			} else {
				System.err.println("Counterexample was NOT present before");
				return true;
			}
		} else {
			return true;
		}

	}
}
