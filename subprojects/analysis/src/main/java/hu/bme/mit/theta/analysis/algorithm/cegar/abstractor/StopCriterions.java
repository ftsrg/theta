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
package hu.bme.mit.theta.analysis.algorithm.cegar.abstractor;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.common.Utils;

import java.util.Collection;

/**
 * Implementations for different stop criterions.
 */
public final class StopCriterions {

	private StopCriterions() {
	}

	/**
	 * @return Criterion that stops at the first counterexample
	 */
	public static <S extends State, A extends Action> StopCriterion<S, A> firstCex() {
		return new FirstCex<>();
	}

	/**
	 * @return Criterion that explores the whole state space
	 */
	public static <S extends State, A extends Action> StopCriterion<S, A> fullExploration() {
		return new FullExploration<>();
	}

	/**
	 * @param n Number of counterexamples to collect
	 * @return Criterion that stops after a given number of counterexamples
	 */
	public static <S extends State, A extends Action> StopCriterion<S, A> atLeastNCexs(final int n) {
		return new AtLeastNCexs<>(n);
	}

	private static final class FirstCex<S extends State, A extends Action> implements StopCriterion<S, A> {
		@Override
		public boolean canStop(final ARG<S, A> arg) {
			return arg.getUnsafeNodes().findAny().isPresent();
		}

		@Override
		public boolean canStop(ARG<S, A> arg, Collection<ArgNode<S, A>> newNodes) {
			return newNodes.stream().anyMatch(n -> n.isTarget() && !n.isExcluded());
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder(StopCriterion.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}

	private static final class FullExploration<S extends State, A extends Action> implements StopCriterion<S, A> {
		@Override
		public boolean canStop(final ARG<S, A> arg) {
			return false;
		}

		@Override
		public boolean canStop(ARG<S, A> arg, Collection<ArgNode<S, A>> newNodes) {
			return false;
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder(StopCriterion.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}

	private static final class AtLeastNCexs<S extends State, A extends Action> implements StopCriterion<S, A> {
		private final int n;

		private AtLeastNCexs(final int n) {
			checkArgument(n > 0, "n must be positive.");
			this.n = n;
		}

		@Override
		public boolean canStop(final ARG<S, A> arg) {
			// TODO: this could be optimized: we don't need to count it,
			// we just need to know if there are >= n elements
			return arg.getUnsafeNodes().count() >= n;
		}

		@Override
		public boolean canStop(ARG<S, A> arg, Collection<ArgNode<S, A>> newNodes) {
			return canStop(arg);
		}

		@Override
		public String toString() {
			return Utils.lispStringBuilder(StopCriterion.class.getSimpleName()).add(getClass().getSimpleName())
					.add("N = " + n).toString();
		}
	}
}
