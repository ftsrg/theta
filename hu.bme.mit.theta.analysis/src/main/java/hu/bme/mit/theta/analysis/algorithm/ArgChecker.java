package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toSet;

import java.util.Collection;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprDomain;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStateUtils;
import hu.bme.mit.theta.solver.Solver;

public final class ArgChecker {

	private final Solver solver;
	private final Domain<ExprState> domain;

	private ArgChecker(final Solver solver) {
		this.solver = checkNotNull(solver);
		domain = ExprDomain.create(solver);
	}

	public static ArgChecker create(final Solver solver) {
		return new ArgChecker(solver);
	}

	////

	public boolean isUnwinding(final ARG<?, ?> arg) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	public boolean isWellLabeled(final ARG<? extends ExprState, ? extends ExprAction> arg) {
		return arg.getInitNodes().allMatch(this::subtreeIsWellLabeled);
	}

	////

	private boolean subtreeIsWellLabeled(final ArgNode<? extends ExprState, ? extends ExprAction> node) {
		if (nodeIsWellLabeled(node)) {
			return node.getSuccNodes().allMatch(succNode -> subtreeIsWellLabeled(succNode));
		} else {
			return false;
		}
	}

	private boolean nodeIsWellLabeled(final ArgNode<? extends ExprState, ? extends ExprAction> node) {
		return nodeIsWellLabeledForCoverage(node) && nodeIsWellLabeledForActions(node);
	}

	////

	private boolean nodeIsWellLabeledForCoverage(final ArgNode<? extends ExprState, ?> node) {
		final Optional<? extends ArgNode<? extends ExprState, ?>> optCoveringNode = node.getCoveringNode();
		if (optCoveringNode.isPresent()) {
			final ArgNode<? extends ExprState, ?> coveringNode = optCoveringNode.get();
			return isCoveredBy(node, coveringNode) && !coveringNode.isExcluded();
		} else {
			return true;
		}

	}

	private boolean isCoveredBy(final ArgNode<? extends ExprState, ?> node,
			final ArgNode<? extends ExprState, ?> coveringNode) {
		return domain.isLeq(node.getState(), coveringNode.getState());
	}

	////

	private boolean nodeIsWellLabeledForActions(final ArgNode<? extends ExprState, ? extends ExprAction> node) {
		final Set<ExprAction> actions = getActionsForNode(node);
		return actions.stream().allMatch(action -> nodeIsWellLabeledForAction(node, action));
	}

	private boolean nodeIsWellLabeledForAction(final ArgNode<? extends ExprState, ? extends ExprAction> node,
			final ExprAction action) {
		final ExprState state = node.getState();
		final Collection<ExprState> succStates = getSuccStatesOfNodeForAction(node, action);
		return hasSuccStates(state, action, succStates);
	}

	private boolean hasSuccStates(final ExprState state, final ExprAction action,
			final Collection<? extends ExprState> succStates) {
		return !ExprStateUtils.anyUncoveredSuccessor(state, action, succStates, solver).isPresent();
	}

	////

	private static <S extends State, A extends Action> Set<A> getActionsForNode(
			final ArgNode<? extends S, ? extends A> node) {
		return node.getOutEdges().map(e -> e.getAction()).collect(toSet());
	}

	private static <S extends State, A extends Action> Collection<S> getSuccStatesOfNodeForAction(
			final ArgNode<? extends S, ? extends A> node, final A action) {
		return node.outEdges.stream().filter(e -> e.getAction().equals(action)).map(e -> e.getTarget().getState())
				.collect(toList());
	}

}