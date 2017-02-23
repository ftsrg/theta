package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.Collection;
import java.util.Optional;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;

public final class ArgBuilder<S extends State, A extends Action, P extends Prec> {

	private final LTS<? super S, ? extends A> lts;
	private final Analysis<S, ? super A, ? super P> analysis;
	private final Predicate<? super S> target;

	private ArgBuilder(final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target) {
		this.lts = checkNotNull(lts);
		this.analysis = checkNotNull(analysis);
		this.target = checkNotNull(target);
	}

	public static <S extends State, A extends Action, P extends Prec> ArgBuilder<S, A, P> create(
			final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target) {
		return new ArgBuilder<>(lts, analysis, target);
	}

	public ARG<S, A> createArg() {
		return ARG.create(analysis.getDomain());
	}

	public void init(final ARG<S, A> arg, final P prec) {
		checkNotNull(arg);
		checkNotNull(prec);

		final Collection<S> oldInitStates = arg.getInitNodes().map(ArgNode::getState).collect(toList());
		final Collection<? extends S> newInitStates = analysis.getInitFunction().getInitStates(prec);
		for (final S initState : newInitStates) {
			if (oldInitStates.stream().noneMatch(s -> analysis.getDomain().isLeq(initState, s))) {
				final boolean isTarget = target.test(initState);
				arg.createInitNode(initState, isTarget);
			}
		}
		arg.initialized = true;
	}

	public void expand(final ArgNode<S, A> node, final P prec) {
		checkNotNull(node);
		checkNotNull(prec);

		final S state = node.getState();
		final Collection<S> oldSuccStates = node.getSuccStates().collect(toList());
		final Collection<? extends A> actions = lts.getEnabledActionsFor(state);
		for (final A action : actions) {
			final Collection<? extends S> newSuccStates = analysis.getTransferFunction().getSuccStates(state, action,
					prec);
			for (final S newSuccState : newSuccStates) {
				if (oldSuccStates.stream().noneMatch(s -> analysis.getDomain().isLeq(newSuccState, s))) {
					final boolean isTarget = target.test(newSuccState);
					node.arg.createSuccNode(node, action, newSuccState, isTarget);
				}

			}
		}
		node.expanded = true;
	}

	public void close(final ArgNode<S, A> node) {
		checkNotNull(node);
		if (!node.isSubsumed()) {
			final ARG<S, A> arg = node.arg;
			final Optional<ArgNode<S, A>> nodeToCoverWith = arg.getNodes().filter(n -> n.mayCover(node)).findFirst();
			nodeToCoverWith.ifPresent(node::cover);
		}
	}

}
