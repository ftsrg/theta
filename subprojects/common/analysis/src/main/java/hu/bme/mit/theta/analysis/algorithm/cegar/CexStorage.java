package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

import java.util.LinkedHashSet;
import java.util.Set;

public class CexStorage<S extends State, A extends Action> {
	Set<ArgTrace<S, A>> counterexamples = new LinkedHashSet<>();

	public void addCounterexample(ArgTrace<S,A> ctx) {
		counterexamples.add(ctx);
	}

	public boolean checkCounterexample(ArgTrace<S,A> ctx) {
		if(counterexamples.contains(ctx)) {
			System.err.println("Current counterexample was NOT present before");
			return true;
		} else {
			System.err.println("Current counterexample WAS present before");
			return false;
		}
	}
}
