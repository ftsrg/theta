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
package hu.bme.mit.theta.cfa.analysis.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;
import java.util.function.Function;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.reachedset.ReachedSet;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;

public final class ImpactChecker<S extends State, A extends Action, P extends Prec> implements SafetyChecker<S, A, P> {

	private final ArgBuilder<S, A, P> argBuilder;
	private final ImpactRefiner<S, A> refiner;
	private final Function<? super S, ?> partitioning;

	private ImpactChecker(final ArgBuilder<S, A, P> argBuilder, final ImpactRefiner<S, A> refiner,
			final Function<? super S, ?> partitioning) {
		this.argBuilder = checkNotNull(argBuilder);
		this.refiner = checkNotNull(refiner);
		this.partitioning = checkNotNull(partitioning);
	}

	public static <S extends State, A extends Action, P extends Prec> ImpactChecker<S, A, P> create(
			final ArgBuilder<S, A, P> argBuilder, final ImpactRefiner<S, A> refiner,
			final Function<? super S, ?> partitioning) {
		return new ImpactChecker<>(argBuilder, refiner, partitioning);
	}

	////

	@Override
	public SafetyResult<S, A> check(final P prec) {
		return new CheckMethod(prec).run();
	}

	////

	private final class CheckMethod {
		private final P prec;

		private final ARG<S, A> arg;
		private final ReachedSet<S, A> reachedSet;

		private CheckMethod(final P prec) {
			this.prec = checkNotNull(prec);
			arg = argBuilder.createArg();
			reachedSet = ImpactReachedSet.create(partitioning);
		}

		private SafetyResult<S, A> run() {
			final Optional<ArgNode<S, A>> unsafeNode = unwind();

			if (unsafeNode.isPresent()) {
				return SafetyResult.unsafe(ArgTrace.to(unsafeNode.get()).toTrace(), arg);
			} else {
				return SafetyResult.safe(arg);
			}
		}

		////

		private Optional<ArgNode<S, A>> searchForUnsafeNode(final ArgNode<S, A> node) {
			final Waitlist<ArgNode<S, A>> waitlist = FifoWaitlist.create();
			waitlist.add(node);

			while (!waitlist.isEmpty()) {
				final ArgNode<S, A> v = waitlist.remove();
				close(v);
				if (!v.isExcluded()) {
					if (v.isTarget()) {
						refine(v);
						if (v.isFeasible()) {
							return Optional.of(v);
						} else {
							closeProperAncestorsOf(v);
						}
					} else {
						expand(v);
						reachedSet.addAll(v.getSuccNodes());
						waitlist.addAll(v.getSuccNodes());
					}
				}
			}

			return Optional.empty();
		}

		private Optional<ArgNode<S, A>> unwind() {
			argBuilder.init(arg, prec);
			reachedSet.addAll(arg.getInitNodes());

			while (true) {
				final Optional<ArgNode<S, A>> anyIncompleteNode = arg.getIncompleteNodes().findAny();

				if (anyIncompleteNode.isPresent()) {
					final ArgNode<S, A> v = anyIncompleteNode.get();

					assert v.isLeaf();

					closeProperAncestorsOf(v);

					final Optional<ArgNode<S, A>> unsafeDescendant = searchForUnsafeNode(v);
					if (unsafeDescendant.isPresent()) {
						return unsafeDescendant;
					}
				} else {
					return Optional.empty();
				}
			}
		}

		////

		private void close(final ArgNode<S, A> node) {
			reachedSet.tryToCover(node);
		}

		private void closeProperAncestorsOf(final ArgNode<S, A> v) {
			v.properAncestors().forEach(this::close);
		}

		private void expand(final ArgNode<S, A> v) {
			argBuilder.expand(v, prec);
		}

		private void refine(final ArgNode<S, A> v) {
			final ArgTrace<S, A> argTrace = ArgTrace.to(v);

			final Trace<S, A> trace = argTrace.toTrace();
			final ImpactRefiner.RefinementResult<S, A> refinementResult = refiner.refine(trace);

			if (refinementResult.isSuccesful()) {
				final Trace<S, A> refinedTrace = refinementResult.asSuccesful().getTrace();
				for (int i = 0; i < argTrace.nodes().size(); i++) {
					final ArgNode<S, A> vi = argTrace.node(i);
					vi.clearCoveredNodes();
					vi.setState(refinedTrace.getState(i));
				}
			}
		}

	}
}
