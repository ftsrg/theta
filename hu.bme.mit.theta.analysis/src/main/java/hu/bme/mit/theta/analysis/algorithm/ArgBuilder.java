package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

public final class ArgBuilder<S extends State, A extends Action, P extends Precision> {

	private final Analysis<S, A, P> analysis;
	private final Predicate<? super S> target;

	private ArgBuilder(final Analysis<S, A, P> analysis, final Predicate<? super S> target) {
		this.analysis = checkNotNull(analysis);
		this.target = checkNotNull(target);
	}

	public static <S extends State, A extends Action, P extends Precision> ArgBuilder<S, A, P> create(
			final Analysis<S, A, P> analysis, final Predicate<? super S> target) {
		return new ArgBuilder<>(analysis, target);
	}

	public ARG<S, A> createArg(final P precision) {
		checkNotNull(precision);
		final ARG<S, A> arg = new ARG<>();
		final Collection<? extends S> initStates = analysis.getInitFunction().getInitStates(precision);
		for (final S initState : initStates) {
			final boolean isTarget = target.test(initState);
			arg.createInitNode(initState, isTarget);
		}
		return arg;
	}

	public void expandNode(final ArgNode<S, A> node, final P precision) {
		checkNotNull(node);
		checkNotNull(precision);

		final S state = node.getState();
		final Collection<? extends A> actions = analysis.getActionFunction().getEnabledActionsFor(state);
		for (final A action : actions) {
			final Collection<? extends S> succStates = analysis.getTransferFunction().getSuccStates(state, action,
					precision);
			for (final S succState : succStates) {
				final boolean isTarget = target.test(succState);
				node.arg.createSuccNode(node, action, succState, isTarget);
			}
		}
	}

	public void closeNode(final ArgNode<S, A> node) {
		checkNotNull(node);

		final S state = node.getState();
		for (final ArgNode<S, A> nodeToCoverWith : node.arg.getNodes()) {
			if (nodeToCoverWith.getId() >= node.getId()) {
				return;
			}

			if (nodeToCoverWith.isCovered()) {
				continue;
			}

			final S stateToCoverWith = nodeToCoverWith.getState();
			if (analysis.getDomain().isLeq(state, stateToCoverWith)) {
				node.cover(nodeToCoverWith);
				return;
			}
		}
	}

}
