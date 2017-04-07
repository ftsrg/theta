package hu.bme.mit.theta.analysis.xta.algorithm.lazy;

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
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAnalysis;
import hu.bme.mit.theta.analysis.xta.XtaLts;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class LazyXtaChecker<S extends State> implements SafetyChecker<XtaState<S>, XtaAction, UnitPrec> {

	public interface AlgorithmStrategy<S extends State> {
		Analysis<S, XtaAction, UnitPrec> getAnalysis();

		boolean covers(ArgNode<XtaState<S>, XtaAction> nodeToCover, ArgNode<XtaState<S>, XtaAction> coveringNode);

		boolean mightCover(ArgNode<XtaState<S>, XtaAction> nodeToCover, ArgNode<XtaState<S>, XtaAction> coveringNode);

		boolean shouldRefine(ArgNode<XtaState<S>, XtaAction> node);

		Collection<ArgNode<XtaState<S>, XtaAction>> forceCover(ArgNode<XtaState<S>, XtaAction> nodeToCover,
				ArgNode<XtaState<S>, XtaAction> coveringNode, LazyXtaStatistics.Builder statistics);

		Collection<ArgNode<XtaState<S>, XtaAction>> refine(ArgNode<XtaState<S>, XtaAction> node,
				LazyXtaStatistics.Builder statistics);

		void resetState(ArgNode<XtaState<S>, XtaAction> node);
	}

	private final AlgorithmStrategy<S> algorithm;
	private final SearchStrategy search;

	private final ArgBuilder<XtaState<S>, XtaAction, UnitPrec> argBuilder;

	private LazyXtaChecker(final XtaSystem system, final AlgorithmStrategy<S> algorithm, final SearchStrategy search,
			final Predicate<? super List<? extends Loc>> errorLocs) {
		checkNotNull(system);
		checkNotNull(errorLocs);

		this.algorithm = checkNotNull(algorithm);
		this.search = checkNotNull(search);

		final LTS<XtaState<?>, XtaAction> lts = XtaLts.create();
		final Analysis<XtaState<S>, XtaAction, UnitPrec> analysis = XtaAnalysis.create(system, algorithm.getAnalysis());
		final Predicate<XtaState<?>> target = s -> errorLocs.test(s.getLocs());

		argBuilder = ArgBuilder.create(lts, analysis, target);
	}

	public static <S extends State> LazyXtaChecker<S> create(final XtaSystem system,
			final AlgorithmStrategy<S> algorithmStrategy, final SearchStrategy searchStrategy,
			final Predicate<? super List<? extends Loc>> errorLocs) {
		return new LazyXtaChecker<>(system, algorithmStrategy, searchStrategy, errorLocs);
	}

	@Override
	public SafetyResult<XtaState<S>, XtaAction> check(final UnitPrec prec) {
		return new CheckMethod().run();
	}

	private final class CheckMethod {
		private final ARG<XtaState<S>, XtaAction> arg;
		private final Waitlist<ArgNode<XtaState<S>, XtaAction>> waitlist;
		private final Partition<ArgNode<XtaState<S>, XtaAction>, Tuple2<List<Loc>, Valuation>> reachedSet;

		private final LazyXtaStatistics.Builder statistics;

		private CheckMethod() {
			arg = argBuilder.createArg();
			waitlist = search.createWaitlist();
			reachedSet = Partition.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getVal()));

			statistics = LazyXtaStatistics.builder(arg);

			argBuilder.init(arg, UnitPrec.getInstance());
			waitlist.addAll(arg.getInitNodes());
		}

		public SafetyResult<XtaState<S>, XtaAction> run() {
			final Optional<ArgNode<XtaState<S>, XtaAction>> unsafeNode = searchForUnsafeNode();
			if (unsafeNode.isPresent()) {
				final ArgTrace<XtaState<S>, XtaAction> argTrace = ArgTrace.to(unsafeNode.get());
				final Trace<XtaState<S>, XtaAction> trace = argTrace.toTrace();
				final LazyXtaStatistics stats = statistics.build();
				return SafetyResult.unsafe(trace, arg, stats);
			} else {
				final LazyXtaStatistics stats = statistics.build();
				return SafetyResult.safe(arg, stats);
			}
		}

		private Optional<ArgNode<XtaState<S>, XtaAction>> searchForUnsafeNode() {

			statistics.startAlgorithm();

			while (!waitlist.isEmpty()) {
				final ArgNode<XtaState<S>, XtaAction> v = waitlist.remove();
				assert v.isLeaf();

				if (algorithm.shouldRefine(v)) {
					statistics.startRefinement();
					final Collection<ArgNode<XtaState<S>, XtaAction>> uncoveredNodes = algorithm.refine(v, statistics);
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

		private void close(final ArgNode<XtaState<S>, XtaAction> nodeToCover) {
			assert nodeToCover.isLeaf();

			final Collection<ArgNode<XtaState<S>, XtaAction>> candidates = reachedSet.get(nodeToCover);

			if (!candidates.isEmpty()) {
				for (final ArgNode<XtaState<S>, XtaAction> coveringNode : candidates) {
					if (algorithm.covers(nodeToCover, coveringNode)) {
						nodeToCover.setCoveringNode(coveringNode);
						return;
					}
				}

				for (final ArgNode<XtaState<S>, XtaAction> coveringNode : candidates) {
					if (algorithm.mightCover(nodeToCover, coveringNode)) {
						statistics.startRefinement();
						final Collection<ArgNode<XtaState<S>, XtaAction>> uncoveredNodes = algorithm
								.forceCover(nodeToCover, coveringNode, statistics);
						statistics.stopRefinement();
						waitlist.addAll(uncoveredNodes);
						if (algorithm.covers(nodeToCover, coveringNode)) {
							nodeToCover.setCoveringNode(coveringNode);
							return;
						}
					}
				}

				algorithm.resetState(nodeToCover);
			}
		}

		private void expand(final ArgNode<XtaState<S>, XtaAction> v) {
			argBuilder.expand(v, UnitPrec.getInstance());
			reachedSet.add(v);
			waitlist.addAll(v.getSuccNodes());
		}
	}

}
