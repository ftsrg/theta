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
package hu.bme.mit.theta.formalism.xta.analysis.lazy;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Analysis;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.prod2.Prod2State;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.common.product.Tuple;
import hu.bme.mit.theta.common.product.Tuple2;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAction;
import hu.bme.mit.theta.formalism.xta.analysis.XtaAnalysis;
import hu.bme.mit.theta.formalism.xta.analysis.XtaLts;
import hu.bme.mit.theta.formalism.xta.analysis.XtaState;
import hu.bme.mit.theta.formalism.xta.analysis.expl.XtaExplAnalysis;

public final class LazyXtaChecker<S extends State>
		implements SafetyChecker<XtaState<Prod2State<ExplState, S>>, XtaAction, UnitPrec> {

	public interface AlgorithmStrategy<S extends State> {
		Analysis<S, XtaAction, UnitPrec> getAnalysis();

		boolean covers(ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> nodeToCover,
				ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> coveringNode);

		boolean mightCover(ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> nodeToCover,
				ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> coveringNode);

		boolean shouldRefine(ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> node);

		Collection<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> forceCover(
				ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> nodeToCover,
				ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> coveringNode,
				LazyXtaStatistics.Builder statistics);

		Collection<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> refine(
				ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> node, LazyXtaStatistics.Builder statistics);
	}

	private final AlgorithmStrategy<S> algorithm;
	private final SearchStrategy search;

	private final ArgBuilder<XtaState<Prod2State<ExplState, S>>, XtaAction, UnitPrec> argBuilder;

	private LazyXtaChecker(final XtaSystem system, final AlgorithmStrategy<S> algorithm, final SearchStrategy search,
			final Predicate<? super List<? extends Loc>> errorLocs) {
		checkNotNull(system);
		checkNotNull(errorLocs);

		this.algorithm = checkNotNull(algorithm);
		this.search = checkNotNull(search);

		final LTS<XtaState<?>, XtaAction> lts = XtaLts.create(system);
		final Analysis<ExplState, XtaAction, UnitPrec> explAnalysis = XtaExplAnalysis.create(system);

		final Prod2Prec<UnitPrec, UnitPrec> prec = Prod2Prec.of(UnitPrec.getInstance(), UnitPrec.getInstance());
		final Analysis<Prod2State<ExplState, S>, XtaAction, UnitPrec> prodAnalysis = PrecMappingAnalysis
				.create(Prod2Analysis.create(explAnalysis, algorithm.getAnalysis()), u -> prec);
		final Analysis<XtaState<Prod2State<ExplState, S>>, XtaAction, UnitPrec> analysis = XtaAnalysis.create(system,
				prodAnalysis);
		final Predicate<XtaState<?>> target = s -> errorLocs.test(s.getLocs());

		argBuilder = ArgBuilder.create(lts, analysis, target);
	}

	public static <S extends State> LazyXtaChecker<S> create(final XtaSystem system,
			final AlgorithmStrategy<S> algorithmStrategy, final SearchStrategy searchStrategy,
			final Predicate<? super List<? extends Loc>> errorLocs) {
		return new LazyXtaChecker<>(system, algorithmStrategy, searchStrategy, errorLocs);
	}

	@Override
	public SafetyResult<XtaState<Prod2State<ExplState, S>>, XtaAction> check(final UnitPrec prec) {
		return new CheckMethod().run();
	}

	private final class CheckMethod {
		private final ARG<XtaState<Prod2State<ExplState, S>>, XtaAction> arg;
		private final Waitlist<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> waitlist;
		private final Partition<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>, Tuple2<List<Loc>, ExplState>> reachedSet;

		private final LazyXtaStatistics.Builder statistics;

		private CheckMethod() {
			arg = argBuilder.createArg();
			waitlist = search.createWaitlist();
			reachedSet = Partition.of(n -> Tuple.of(n.getState().getLocs(), n.getState().getState()._1()));

			statistics = LazyXtaStatistics.builder(arg);

			argBuilder.init(arg, UnitPrec.getInstance());
			waitlist.addAll(arg.getInitNodes());
		}

		public SafetyResult<XtaState<Prod2State<ExplState, S>>, XtaAction> run() {
			final Optional<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> unsafeNode = searchForUnsafeNode();
			if (unsafeNode.isPresent()) {
				final ArgTrace<XtaState<Prod2State<ExplState, S>>, XtaAction> argTrace = ArgTrace.to(unsafeNode.get());
				final Trace<XtaState<Prod2State<ExplState, S>>, XtaAction> trace = argTrace.toTrace();
				final LazyXtaStatistics stats = statistics.build();
				return SafetyResult.unsafe(trace, arg, stats);
			} else {
				final LazyXtaStatistics stats = statistics.build();
				return SafetyResult.safe(arg, stats);
			}
		}

		private Optional<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> searchForUnsafeNode() {

			statistics.startAlgorithm();

			while (!waitlist.isEmpty()) {
				final ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> v = waitlist.remove();
				assert v.isLeaf();

				if (algorithm.shouldRefine(v)) {
					statistics.startRefinement();
					final Collection<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> uncoveredNodes = algorithm
							.refine(v, statistics);
					statistics.stopRefinement();
					waitlist.addAll(uncoveredNodes);
				} else if (v.isTarget()) {
					statistics.stopAlgorithm();
					return Optional.of(v);
				} else {
					close(v);
					if (!v.isCovered()) {
						expand(v);
					}
				}
			}
			statistics.stopAlgorithm();
			return Optional.empty();
		}

		////

		private void close(final ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> nodeToCover) {
			assert nodeToCover.isLeaf();

			final Collection<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> candidates = reachedSet
					.get(nodeToCover);

			if (!candidates.isEmpty()) {
				for (final ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> coveringNode : candidates) {
					if (algorithm.covers(nodeToCover, coveringNode)) {
						nodeToCover.setCoveringNode(coveringNode);
						return;
					}
				}

				for (final ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> coveringNode : candidates) {
					if (algorithm.mightCover(nodeToCover, coveringNode)) {
						statistics.startRefinement();
						final Collection<ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction>> uncoveredNodes = algorithm
								.forceCover(nodeToCover, coveringNode, statistics);
						statistics.stopRefinement();
						waitlist.addAll(uncoveredNodes);
						if (algorithm.covers(nodeToCover, coveringNode)) {
							nodeToCover.setCoveringNode(coveringNode);
							return;
						}
					}
				}
			}
		}

		private void expand(final ArgNode<XtaState<Prod2State<ExplState, S>>, XtaAction> v) {
			argBuilder.expand(v, UnitPrec.getInstance());
			reachedSet.add(v);
			waitlist.addAll(v.getSuccNodes().filter(n -> !n.getState().getState().isBottom1()));
		}
	}

}
