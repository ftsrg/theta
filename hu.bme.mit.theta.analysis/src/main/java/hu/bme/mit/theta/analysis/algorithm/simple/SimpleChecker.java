package hu.bme.mit.theta.analysis.algorithm.simple;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedList;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

public class SimpleChecker {

	public static <S extends State, A extends Action, P extends Precision> boolean run(final Analysis<S, A, P> analysis,
			final Predicate<? super S> target, final P precision) {

		final Deque<S> waiting = new ArrayDeque<>(100000);
		final Collection<S> passed = new LinkedList<>();

		final Collection<? extends S> initStates = analysis.getInitFunction().getInitStates(precision);
		waiting.addAll(initStates);

		while (!waiting.isEmpty()) {
			final S state = waiting.pop();

			if (target.test(state)) {
				return false;
			}

			if (passed.stream().allMatch(s -> !analysis.getDomain().isLeq(state, s))) {
				passed.add(state);
				System.out.println(passed.size());
				for (final A action : analysis.getActionFunction().getEnabledActionsFor(state)) {
					final Collection<? extends S> succStates = analysis.getTransferFunction().getSuccStates(state,
							action, precision);
					for (final S succState : succStates) {
						waiting.add(succState);
					}
				}
			}
		}

		return true;
	}

}
