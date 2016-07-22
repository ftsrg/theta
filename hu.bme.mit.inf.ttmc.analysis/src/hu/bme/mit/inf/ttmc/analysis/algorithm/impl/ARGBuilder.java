package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.function.Predicate;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.ActionFunction;
import hu.bme.mit.inf.ttmc.analysis.Domain;
import hu.bme.mit.inf.ttmc.analysis.InitFunction;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.TransferFunction;

class ARGBuilder<S extends State, A extends Action> {

	final ActionFunction<? super S, ? extends A> actionFunction;

	private final Domain<S> domain;
	private final Predicate<? super S> target;

	ARGBuilder(final Domain<S> domain, final ActionFunction<? super S, ? extends A> actionFunction,
			final Predicate<? super S> target) {
		this.domain = checkNotNull(domain);
		this.actionFunction = checkNotNull(actionFunction);
		this.target = checkNotNull(target);
	}

	public <P extends Precision> ARG<S, A> create(final InitFunction<S, P> initFunction, final P precision) {
		checkNotNull(initFunction);
		checkNotNull(precision);

		final Collection<? extends S> initStates = initFunction.getInitStates(precision);
		final ARG<S, A> arg = new ARG<>(domain);

		for (final S initState : initStates) {
			final boolean isTarget = target.test(initState);
			arg.createInitNode(initState, isTarget);
		}

		return arg;
	}

	public <P extends Precision> void expand(final ARG<S, A> arg, final ARGNode<S, A> node,
			final TransferFunction<S, A, P> transferFunction, final P precision) {
		checkNotNull(arg);
		checkNotNull(node);
		checkNotNull(transferFunction);
		checkNotNull(precision);

		if (node.isExpanded() || domain.isBottom(node.getState())) {
			return;
		}

		final S state = node.getState();
		final Collection<? extends A> actions = actionFunction.getEnabledActionsFor(state);
		for (final A action : actions) {
			final Collection<? extends S> succStates = transferFunction.getSuccStates(state, action, precision);
			for (final S succState : succStates) {
				final boolean isTarget = target.test(succState);
				arg.createSuccNode(node, action, succState, isTarget);
			}
		}

		node.expanded = true;
	}

}
