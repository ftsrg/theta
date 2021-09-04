package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

import java.util.LinkedHashSet;
import java.util.Set;

public class CexStorage<S extends State, A extends Action> {
	Set<Integer> counterexamples = new LinkedHashSet<>();

	public void addCounterexample(ArgTrace<S,A> cex) {
		counterexamples.add(cex.hashCode());
	}

	public boolean checkIfCounterexampleNew(ArgTrace<S,A> cex) {
		if(counterexamples.contains(cex)) {
			System.err.println("Counterexample WAS present before");
			return false;
		} else {
			System.err.println("Counterexample was NOT present before");
			return true;
		}
	}
}
