package hu.bme.mit.theta.analysis.xta.algorithm.lu;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;

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
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.xta.XtaAction;
import hu.bme.mit.theta.analysis.xta.XtaAnalysis;
import hu.bme.mit.theta.analysis.xta.XtaLts;
import hu.bme.mit.theta.analysis.xta.XtaState;
import hu.bme.mit.theta.analysis.xta.algorithm.itp.XtaItpStatistics;
import hu.bme.mit.theta.analysis.xta.zone.XtaZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.analysis.zone.lu.BoundFunction;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneAnalysis;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneDomain;
import hu.bme.mit.theta.analysis.zone.lu.LuZoneState;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.model.impl.Valuation;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;
import hu.bme.mit.theta.formalism.xta.XtaSystem;

public final class XtaLuChecker implements SafetyChecker<XtaState<LuZoneState>, XtaAction, UnitPrec> {
	private final XtaSystem system;
	private final ArgBuilder<XtaState<LuZoneState>, XtaAction, UnitPrec> argBuilder;
	private final SearchStrategy strategy;

	private XtaLuChecker(final XtaSystem system, final Predicate<? super List<? extends Loc>> errorLocs,
			final SearchStrategy strategy) {
		checkNotNull(errorLocs);

		this.system = checkNotNull(system);
		this.strategy = checkNotNull(strategy);

		final LTS<XtaState<?>, XtaAction> lts = XtaLts.create();
		final ZonePrec prec = ZonePrec.of(system.getClocks());
		final Analysis<XtaState<LuZoneState>, XtaAction, UnitPrec> analysis = XtaAnalysis.create(system,
				PrecMappingAnalysis.create(LuZoneAnalysis.create(XtaZoneAnalysis.getInstance()), u -> prec));
		final Predicate<XtaState<?>> target = s -> errorLocs.test(s.getLocs());

		argBuilder = ArgBuilder.create(lts, analysis, target);
	}

	public static XtaLuChecker create(final XtaSystem system, final Predicate<? super List<? extends Loc>> errorLocs,
			final SearchStrategy strategy) {
		return new XtaLuChecker(system, errorLocs, strategy);
	}

	@Override
	public SafetyResult<XtaState<LuZoneState>, XtaAction> check(final UnitPrec prec) {
		return new CheckMethod().run();
	}

	private final class CheckMethod {
		private final ARG<XtaState<LuZoneState>, XtaAction> arg;
		private final Waitlist<ArgNode<XtaState<LuZoneState>, XtaAction>> waitlist;
		private final Partition<ArgNode<XtaState<LuZoneState>, XtaAction>, Tuple2<List<Loc>, Valuation>> reachedSet;

		private final XtaItpStatistics.Builder statisticsBuilder;

		private final XtaLuRefiner refiner;

		private CheckMethod() {
			arg = argBuilder.createArg();
			waitlist = strategy.createWaitlist();
			reachedSet = Partition.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getVal()));

			statisticsBuilder = XtaItpStatistics.builder(arg);

			refiner = XtaLuRefiner.create(system, waitlist, statisticsBuilder);

			argBuilder.init(arg, UnitPrec.getInstance());
			waitlist.addAll(arg.getInitNodes());
		}

		public SafetyResult<XtaState<LuZoneState>, XtaAction> run() {
			final Optional<ArgNode<XtaState<LuZoneState>, XtaAction>> unsafeNode = searchForUnsafeNode();
			if (unsafeNode.isPresent()) {
				final ArgTrace<XtaState<LuZoneState>, XtaAction> argTrace = ArgTrace.to(unsafeNode.get());
				final Trace<XtaState<LuZoneState>, XtaAction> trace = argTrace.toTrace();
				final XtaItpStatistics stats = statisticsBuilder.build();
				return SafetyResult.unsafe(trace, arg, stats);
			} else {
				final XtaItpStatistics stats = statisticsBuilder.build();
				return SafetyResult.safe(arg, stats);
			}
		}

		private Optional<ArgNode<XtaState<LuZoneState>, XtaAction>> searchForUnsafeNode() {

			statisticsBuilder.startAlgorithm();

			while (!waitlist.isEmpty()) {
				final ArgNode<XtaState<LuZoneState>, XtaAction> v = waitlist.remove();
				assert v.isLeaf();

				final ZoneState concreteZone = v.getState().getState().getZone();

				if (concreteZone.isBottom()) {
					refiner.refine(v, BoundFunction.top());
				} else if (v.isTarget()) {
					statisticsBuilder.stopAlgorithm();
					return Optional.of(v);
				} else {
					close(v);
					if (!v.isCovered()) {
						expand(v);
					}
				}
			}
			statisticsBuilder.stopAlgorithm();
			return Optional.empty();
		}

		////

		private void close(final ArgNode<XtaState<LuZoneState>, XtaAction> node) {
			assert node.isLeaf();

			final Collection<ArgNode<XtaState<LuZoneState>, XtaAction>> candidates = reachedSet.get(node);

			for (final ArgNode<XtaState<LuZoneState>, XtaAction> nodeToCoverWith : candidates) {
				if (covers(nodeToCoverWith.getState(), node.getState())) {
					node.setCoveringNode(nodeToCoverWith);
					return;
				}
			}

			for (final ArgNode<XtaState<LuZoneState>, XtaAction> nodeToCoverWith : candidates) {
				if (couldCover(nodeToCoverWith.getState(), node.getState())) {
					refiner.refine(node, nodeToCoverWith.getState().getState().getBoundFunction());
					if (covers(nodeToCoverWith.getState(), node.getState())) {
						node.setCoveringNode(nodeToCoverWith);
						return;
					}
				}
			}

		}

		private void expand(final ArgNode<XtaState<LuZoneState>, XtaAction> v) {
			argBuilder.expand(v, UnitPrec.getInstance());
			reachedSet.add(v);
			waitlist.addAll(v.getSuccNodes());
		}

		private boolean covers(final XtaState<LuZoneState> state1, final XtaState<LuZoneState> state2) {
			return LuZoneDomain.getInstance().isLeq(state1.getState(), state2.getState());
		}

		private boolean couldCover(final XtaState<LuZoneState> state1, final XtaState<LuZoneState> state2) {
			return LuZoneDomain.getInstance().zoneIsLeq(state1.getState().getZone(), state2.getState());
		}

	}

}
