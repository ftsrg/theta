package hu.bme.mit.theta.analysis.xta.algorithm.itp;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.TimeUnit;
import java.util.function.Predicate;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAnalysis;
import hu.bme.mit.theta.analysis.xta.XtaLts;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.itp.ItpZoneState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaItpChecker implements SafetyChecker<XtaState<ItpZoneState>, XtaAction, UnitPrec> {
	private final XtaSystem system;
	private final ArgBuilder<XtaState<ItpZoneState>, XtaAction, UnitPrec> argBuilder;
	private final SearchStrategy strategy;

	private XtaItpChecker(final XtaSystem system, final Predicate<? super List<? extends Loc>> errorLocs,
			final SearchStrategy strategy) {
		checkNotNull(errorLocs);

		this.system = checkNotNull(system);
		this.strategy = checkNotNull(strategy);

		final LTS<XtaState<?>, XtaAction> lts = XtaLts.create();
		final ZonePrec prec = ZonePrec.of(system.getClocks());
		final Analysis<XtaState<ItpZoneState>, XtaAction, UnitPrec> analysis = XtaAnalysis.create(system,
				PrecMappingAnalysis.create(ItpZoneAnalysis.create(XtaZoneAnalysis.getInstance()), u -> prec));
		final Predicate<XtaState<?>> target = s -> errorLocs.test(s.getLocs());

		argBuilder = ArgBuilder.create(lts, analysis, target);
	}

	public static XtaItpChecker create(final XtaSystem system, final Predicate<? super List<? extends Loc>> errorLocs,
			final SearchStrategy strategy) {
		return new XtaItpChecker(system, errorLocs, strategy);
	}

	@Override
	public SafetyResult<XtaState<ItpZoneState>, XtaAction> check(final UnitPrec prec) {
		return new CheckMethod().run();
	}

	private final class CheckMethod {
		private final ARG<XtaState<ItpZoneState>, XtaAction> arg;
		private final Waitlist<ArgNode<XtaState<ItpZoneState>, XtaAction>> waitlist;
		private final Partition<ArgNode<XtaState<ItpZoneState>, XtaAction>, Tuple2<List<Loc>, Valuation>> reachedSet;
		private final XtaItpRefiner refiner;

		private int refinements = 0;

		private CheckMethod() {
			waitlist = strategy.createWaitlist();
			reachedSet = Partition.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getVal()));
			refiner = XtaItpRefiner.create(system, waitlist);
			arg = argBuilder.createArg();

			argBuilder.init(arg, UnitPrec.getInstance());
			waitlist.addAll(arg.getInitNodes());
		}

		public SafetyResult<XtaState<ItpZoneState>, XtaAction> run() {
			final Stopwatch stopwatch = Stopwatch.createStarted();
			final Optional<ArgNode<XtaState<ItpZoneState>, XtaAction>> unsafeNode = searchForUnsafeNode();
			if (unsafeNode.isPresent()) {
				final ArgTrace<XtaState<ItpZoneState>, XtaAction> argTrace = ArgTrace.to(unsafeNode.get());
				final Trace<XtaState<ItpZoneState>, XtaAction> trace = argTrace.toTrace();
				final Statistics stats = new Statistics(stopwatch.elapsed(TimeUnit.MILLISECONDS), refinements);
				return SafetyResult.unsafe(trace, arg, stats);
			} else {
				final Statistics stats = new Statistics(stopwatch.elapsed(TimeUnit.MILLISECONDS), refinements);
				return SafetyResult.safe(arg, stats);
			}
		}

		private Optional<ArgNode<XtaState<ItpZoneState>, XtaAction>> searchForUnsafeNode() {
			while (!waitlist.isEmpty()) {
				final ArgNode<XtaState<ItpZoneState>, XtaAction> v = waitlist.remove();
				assert v.isLeaf();

				final ZoneState concreteZone = v.getState().getState().getZone();

				if (concreteZone.isBottom()) {
					refiner.enforceZone(v, ZoneState.bottom());
					refinements++;
				} else if (v.isTarget()) {
					return Optional.of(v);
				} else {
					close(v);
					if (!v.isCovered()) {
						expand(v);
					}
				}
			}
			return Optional.empty();
		}

		////

		private void close(final ArgNode<XtaState<ItpZoneState>, XtaAction> node) {
			assert node.isLeaf();

			final Collection<ArgNode<XtaState<ItpZoneState>, XtaAction>> candidates = reachedSet.get(node);

			for (final ArgNode<XtaState<ItpZoneState>, XtaAction> nodeToCoverWith : candidates) {
				if (covers(nodeToCoverWith.getState(), node.getState())) {
					node.setCoveringNode(nodeToCoverWith);
					return;
				}
			}

			for (final ArgNode<XtaState<ItpZoneState>, XtaAction> nodeToCoverWith : candidates) {
				if (couldCover(nodeToCoverWith.getState(), node.getState())) {
					refiner.enforceZone(node, nodeToCoverWith.getState().getState().getInterpolant());
					refinements++;
					if (covers(nodeToCoverWith.getState(), node.getState())) {
						node.setCoveringNode(nodeToCoverWith);
						return;
					}
				}
			}

		}

		private void expand(final ArgNode<XtaState<ItpZoneState>, XtaAction> v) {
			argBuilder.expand(v, UnitPrec.getInstance());
			reachedSet.add(v);
			waitlist.addAll(v.getSuccNodes());
		}

		private boolean covers(final XtaState<ItpZoneState> state1, final XtaState<ItpZoneState> state2) {
			return state2.getLocs().equals(state1.getLocs()) && state2.getVal().equals(state2.getVal())
					&& state2.getState().getInterpolant().isLeq(state1.getState().getInterpolant());
		}

		private boolean couldCover(final XtaState<ItpZoneState> state1, final XtaState<ItpZoneState> state2) {
			return state2.getLocs().equals(state1.getLocs()) && state2.getVal().equals(state2.getVal())
					&& state2.getState().getZone().isLeq(state1.getState().getInterpolant());
		}

	}

}
