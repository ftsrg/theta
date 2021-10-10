package hu.bme.mit.theta.analysis.algorithm.runtimecheck;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static com.google.common.base.Preconditions.checkState;

/**
 * CexStorage to be used in configurations, where refinement starts after each counterexample discovered coutnerexample
 * e.g. not MULTI_SEQ refinement, but SEQ_ITP, UNSAT_CORE, etc.
 */
public class SingleCexStorage<S extends State, A extends Action> extends CexStorage<S,A> {
	private final Set<Integer> counterexamples = new LinkedHashSet<>();
	private final Set<Integer> argprecs = new LinkedHashSet<>();
	private Integer currentArgHash = null;

	<P extends Prec> void setCurrentArg(AbstractArg<S,A,P> arg) {
		currentArgHash = arg.hashCode();
	}

	void addCounterexample(ArgTrace<S,A> cex) {
		checkState(currentArgHash!=null);
		int cexHashCode = cex.hashCode();
		counterexamples.add(cexHashCode);
		argprecs.add(currentArgHash);
	}

	boolean checkIfCounterexampleNew(ArgTrace<S,A> cex) {
		checkState(currentArgHash!=null);
		int cexHashCode = cex.hashCode();
		if(argprecs.contains(currentArgHash)) {
			if(counterexamples.contains(cexHashCode)) {
				return false;
			}
		}

		return true;
	}

	@Override
	<P extends Prec> boolean check(ARG<S, A> arg, P prec) {
		return arg.getCexs().noneMatch(this::checkIfCounterexampleNew);
	}
}