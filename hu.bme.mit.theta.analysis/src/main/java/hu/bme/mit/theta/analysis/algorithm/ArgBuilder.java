package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.Optional;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;

public final class ArgBuilder<S extends State, A extends Action, P extends Precision> {

	private final LTS<? super S, ? extends A> lts;
	private final Analysis<S, ? super A, ? super P> analysis;
	private final Predicate<? super S> target;

	private ArgBuilder(final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target) {
		this.lts = checkNotNull(lts);
		this.analysis = checkNotNull(analysis);
		this.target = checkNotNull(target);
	}

	public static <S extends State, A extends Action, P extends Precision> ArgBuilder<S, A, P> create(
			final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target) {
		return new ArgBuilder<>(lts, analysis, target);
	}

	public void init(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);

		final Collection<S> oldInitStates = arg.getInitNodes().map(ArgNode::getState).collect(Collectors.toSet());
		final Collection<? extends S> newInitStates = analysis.getInitFunction().getInitStates(precision);
		for (final S initState : newInitStates) {
			if (oldInitStates.isEmpty()
					|| !oldInitStates.stream().anyMatch(s -> analysis.getDomain().isLeq(initState, s))) {
				final boolean isTarget = target.test(initState);
				arg.createInitNode(initState, isTarget);
			}
		}
		arg.initialized = true;
	}

	public void expand(final ArgNode<S, A> node, final P precision) {
		checkNotNull(node);
		checkNotNull(precision);

		final S state = node.getState();
		final Collection<S> oldSuccStates = node.getSuccStates().collect(Collectors.toSet());
		final Collection<? extends A> actions = lts.getEnabledActionsFor(state);
		for (final A action : actions) {
			final Collection<? extends S> newSuccStates = analysis.getTransferFunction().getSuccStates(state, action,
					precision);
			for (final S newSuccState : newSuccStates) {
				if (oldSuccStates.isEmpty()
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
		if (!node.isCovered()) {
			final ARG<S, A> arg = node.arg;
			final Optional<ArgNode<S, A>> nodeToCoverWith = arg.getNodes().filter(n -> mayCover(n, node)).findFirst();
			nodeToCoverWith.ifPresent(n -> arg.cover(node, n));
		}
	}

	private boolean mayCover(final ArgNode<S, A> nodeToCoverWith, final ArgNode<S, A> node) {
		if (nodeToCoverWith.getId() < node.getId()) {
			final S state = node.getState();
			final S stateToCoverWith = nodeToCoverWith.getState();
			if (analysis.getDomain().isLeq(state, stateToCoverWith)) {
				if (!nodeToCoverWith.isCovered()) {
					return true;
				}
			}
		}
		return false;
	}

}
