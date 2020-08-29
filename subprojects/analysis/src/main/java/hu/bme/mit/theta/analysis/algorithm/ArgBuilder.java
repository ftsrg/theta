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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Optional;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.TransFunc;

/**
 * Helper class for building the ARG with a given analysis and precision.
 */
public final class ArgBuilder<S extends State, A extends Action, P extends Prec> {

	private final LTS<? super S, ? extends A> lts;
	private final Analysis<S, ? super A, ? super P> analysis;
	private final Predicate<? super S> target;
	private final boolean excludeBottom;

	private ArgBuilder(final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
					   final Predicate<? super S> target, final boolean excludeBottom) {
		this.lts = checkNotNull(lts);
		this.analysis = checkNotNull(analysis);
		this.target = checkNotNull(target);
		this.excludeBottom = excludeBottom;
	}

	public static <S extends State, A extends Action, P extends Prec> ArgBuilder<S, A, P> create(
			final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target, final boolean excludeBottom) {
		return new ArgBuilder<>(lts, analysis, target, excludeBottom);
	}

	public static <S extends State, A extends Action, P extends Prec> ArgBuilder<S, A, P> create(
			final LTS<? super S, ? extends A> lts, final Analysis<S, ? super A, ? super P> analysis,
			final Predicate<? super S> target) {
		return create(lts, analysis, target, false);
	}

	public ARG<S, A> createArg() {
		return ARG.create(analysis.getPartialOrd());
	}

	public Collection<ArgNode<S, A>> init(final ARG<S, A> arg, final P prec) {
		checkNotNull(arg);
		checkNotNull(prec);

		final Collection<ArgNode<S, A>> newInitNodes = new ArrayList<>();

		final Collection<? extends S> initStates = analysis.getInitFunc().getInitStates(prec);
		for (final S initState : initStates) {
			if (excludeBottom && initState.isBottom()) {
				continue;
			}
			if (arg.getInitStates().noneMatch(s -> analysis.getPartialOrd().isLeq(initState, s))) {
				final boolean isTarget = target.test(initState);
				final ArgNode<S, A> newNode = arg.createInitNode(initState, isTarget);
				newInitNodes.add(newNode);
			}
		}
		arg.initialized = true;

		return newInitNodes;
	}

	public Collection<ArgNode<S, A>> expand(final ArgNode<S, A> node, final P prec) {
		checkNotNull(node);
		checkNotNull(prec);

		final Collection<ArgNode<S, A>> newSuccNodes = new ArrayList<>();
		final S state = node.getState();
		final Collection<? extends A> actions = lts.getEnabledActionsFor(state);
		final TransFunc<S, ? super A, ? super P> transFunc = analysis.getTransFunc();
		for (final A action : actions) {
			final Collection<? extends S> succStates = transFunc.getSuccStates(state, action, prec);
			for (final S succState : succStates) {
				if (excludeBottom && succState.isBottom()) {
					continue;
				}
				// Only add state if there is no covering sibling (with the same action)
				if (node.getSuccNodes().noneMatch(n -> n.getInEdge().get().getAction().equals(action) &&
						analysis.getPartialOrd().isLeq(succState, n.getState()))) {
					final boolean isTarget = target.test(succState);
					final ArgNode<S, A> newNode = node.arg.createSuccNode(node, action, succState, isTarget);
					newSuccNodes.add(newNode);
				}
			}
		}
		node.expanded = true;

		return newSuccNodes;
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
