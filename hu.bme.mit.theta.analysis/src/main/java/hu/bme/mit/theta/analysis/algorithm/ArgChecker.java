/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toSet;

import java.util.Collection;
import java.util.Optional;
import java.util.Set;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprOrd;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprStateUtils;
import hu.bme.mit.theta.solver.Solver;

public final class ArgChecker {

	private final Solver solver;
	private final PartialOrd<ExprState> partialOrd;

	private ArgChecker(final Solver solver) {
		this.solver = checkNotNull(solver);
		partialOrd = ExprOrd.create(solver);
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
			return node.getSuccNodes().allMatch(this::subtreeIsWellLabeled);
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
		return partialOrd.isLeq(node.getState(), coveringNode.getState());
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
		return node.getOutEdges().map(ArgEdge::getAction).collect(toSet());
	}

	private static <S extends State, A extends Action> Collection<S> getSuccStatesOfNodeForAction(
			final ArgNode<? extends S, ? extends A> node, final A action) {
		return node.outEdges.stream().filter(e -> e.getAction().equals(action)).map(e -> e.getTarget().getState())
				.collect(toList());
	}

}
