package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Predicate;
import java.util.stream.Collectors;

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

	public void init(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);

		final Collection<S> oldInitStates = arg.getInitNodes().map(ArgNode::getState).collect(Collectors.toSet());
		final Collection<? extends S> newInitStates = analysis.getInitFunction().getInitStates(precision);
		for (final S initState : newInitStates) {
			if (oldInitStates.size() == 0
					|| !oldInitStates.stream().anyMatch(s -> analysis.getDomain().isLeq(initState, s))) {
				final boolean isTarget = target.test(initState);
				arg.createInitNode(initState, isTarget);
			}
		}
	}

	public void expand(final ArgNode<S, A> node, final P precision) {
		checkNotNull(node);
		checkNotNull(precision);

		final S state = node.getState();
		final Collection<S> oldSuccStates = node.getSuccStates();
		final Collection<? extends A> actions = analysis.getActionFunction().getEnabledActionsFor(state);
		for (final A action : actions) {
			final Collection<? extends S> newSuccStates = analysis.getTransferFunction().getSuccStates(state, action,
					precision);
			for (final S newSuccState : newSuccStates) {
				if (oldSuccStates.size() == 0
						|| !oldSuccStates.stream().anyMatch(s -> analysis.getDomain().isLeq(newSuccState, s))) {
					final boolean isTarget = target.test(newSuccState);
					node.arg.createSuccNode(node, action, newSuccState, isTarget);
				}

			}
		}
		node.expanded = true;
	}

	public void close(final ArgNode<S, A> node) {
		checkNotNull(node);

		final ARG<S, A> arg = node.arg;
		final S state = node.getState();

		arg.getNodes().forEach(nodeToCoverWith -> {
			if (nodeToCoverWith.getId() >= node.getId()) {
				return;
			}

			final S stateToCoverWith = nodeToCoverWith.getState();

			if (analysis.getDomain().isLeq(state, stateToCoverWith)) {
				if (!nodeToCoverWith.isCovered()) {
					arg.cover(node, nodeToCoverWith);
					return;
				}
			}
		});
	}

	public void pruneAndExpand(final ArgNode<S, A> node, final P newPrecision) {
		checkNotNull(node);
		checkNotNull(newPrecision);

		final ARG<S, A> arg = node.arg;
		arg.prune(node);

		if (node.getInEdge().isPresent()) {
			final ArgEdge<S, A> edge = node.getInEdge().get();
			final ArgNode<S, A> parent = edge.getSource();
			expand(parent, newPrecision);
		} else {
			init(arg, newPrecision);
		}
	}

}
