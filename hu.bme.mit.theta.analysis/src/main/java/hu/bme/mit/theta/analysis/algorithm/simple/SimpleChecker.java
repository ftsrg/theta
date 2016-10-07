package hu.bme.mit.theta.analysis.algorithm.simple;

import java.util.Collection;
import java.util.LinkedList;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.LifoWaitlist;
import hu.bme.mit.theta.analysis.algorithm.Waitlist;

public class SimpleChecker {

	public static <S extends State, A extends Action, P extends Precision> boolean run(final Analysis<S, A, P> analysis,
			final Predicate<? super S> target, final P precision) {

		final Waitlist<S> waiting = new LifoWaitlist<>();
		final Collection<S> passed = new LinkedList<>();

		final Collection<? extends S> initStates = analysis.getInitFunction().getInitStates(precision);
		waiting.addAll(initStates);

		while (!waiting.isEmpty()) {
			final S state = waiting.remove();

			if (target.test(state)) {
				return false;
			}

			if (passed.stream().allMatch(s -> !analysis.getDomain().isLeq(state, s))) {
				passed.add(state);
				System.out.println(passed.size());
				for (final A action : analysis.getActionFunction().getEnabledActionsFor(state)) {
					final Collection<? extends S> succStates = analysis.getTransferFunction().getSuccStates(state,
							action, precision);
					waiting.addAll(succStates);
				}
			}
		}

		return true;
	}

}
