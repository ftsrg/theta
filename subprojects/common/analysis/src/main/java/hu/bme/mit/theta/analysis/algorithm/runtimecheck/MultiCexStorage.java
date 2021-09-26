package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

import java.util.LinkedHashSet;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

/**
 * CexStorage to be used in configurations, where refinement only starts after every counterexample has been discovered
 * (and the ARG has an empty waitlist)
 * e.g. MULTI_SEQ refinement
 * This class only stores ARG hashes, it does not store counterexample hashes
 */
public class MultiCexStorage<S extends State, A extends Action> extends CexStorage<S,A> {
	private final Set<Integer> argHashes = new LinkedHashSet<>();

	<P extends Prec> void setCurrentArg(AbstractArg<S,A,P> arg) {
		int hash = arg.hashCode();
		argHashes.add(hash);
	}

	void addCounterexample(ArgTrace<S,A> cex) {
		// do nothing
	}

	private <P extends Prec> boolean checkIfArgNew(AbstractArg<S,A,P> arg) {
		return argHashes.contains(arg.hashCode());
	}

	@Override
	<P extends Prec> boolean check(ARG<S, A> arg, P prec) {
		return checkIfArgNew(new AbstractArg<>(arg, prec));
	}

	@Override
	boolean checkIfCounterexampleNew(ArgTrace<S, A> cex) {
		return true; // always return true
	}


}
