package hu.bme.mit.theta.analysis.xta.algorithm.itp;

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
import hu.bme.mit.theta.analysis.algorithm.ArgNodeComparators;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.impl.PrecMappingAnalysis;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.unit.UnitPrec;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
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

	private XtaItpChecker(final XtaSystem system, final Predicate<? super List<? extends Loc>> errorLocs) {
		checkNotNull(errorLocs);

		this.system = checkNotNull(system);

		final LTS<XtaState<?>, XtaAction> lts = XtaLts.create();
		final ZonePrec prec = ZonePrec.of(system.getClocks());
		final Analysis<XtaState<ItpZoneState>, XtaAction, UnitPrec> analysis = XtaAnalysis.create(system,
				PrecMappingAnalysis.create(ItpZoneAnalysis.create(XtaZoneAnalysis.getInstance()), u -> prec));
		final Predicate<XtaState<?>> target = s -> errorLocs.test(s.getLocs());

		argBuilder = ArgBuilder.create(lts, analysis, target);
	}

	public static XtaItpChecker create(final XtaSystem system, final Predicate<? super List<? extends Loc>> errorLocs) {
		return new XtaItpChecker(system, errorLocs);
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

		private CheckMethod() {
			waitlist = PriorityWaitlist.create(ArgNodeComparators.bfs());
			reachedSet = Partition.of(n -> Tuple2.of(n.getState().getLocs(), n.getState().getVal()));
			refiner = XtaItpRefiner.create(system, waitlist);
			arg = argBuilder.createArg();

			argBuilder.init(arg, UnitPrec.getInstance());
			waitlist.addAll(arg.getInitNodes());
			reachedSet.addAll(arg.getInitNodes());
		}

		public SafetyResult<XtaState<ItpZoneState>, XtaAction> run() {
			final Optional<ArgNode<XtaState<ItpZoneState>, XtaAction>> unsafeNode = searchForUnsafeNode();
			if (unsafeNode.isPresent()) {
				final ArgTrace<XtaState<ItpZoneState>, XtaAction> argTrace = ArgTrace.to(unsafeNode.get());
				final Trace<XtaState<ItpZoneState>, XtaAction> trace = argTrace.toTrace();
				return SafetyResult.unsafe(trace, arg);
			} else {
				return SafetyResult.safe(arg);
			}
		}

		private Optional<ArgNode<XtaState<ItpZoneState>, XtaAction>> searchForUnsafeNode() {
			while (!waitlist.isEmpty()) {
				final ArgNode<XtaState<ItpZoneState>, XtaAction> v = waitlist.remove();
				assert v.isLeaf();

				final ZoneState concreteZone = v.getState().getState().getZone();

				if (concreteZone.isBottom()) {
					refiner.enforceZone(v, ZoneState.bottom());
				} else if (v.isTarget()) {
					return Optional.of(v);
				} else {
					close(v);
					if (!v.isCovered()) {
						expand(v);
						reachedSet.addAll(v.getSuccNodes());
						waitlist.addAll(v.getSuccNodes());
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
				if (node != nodeToCoverWith) {
					if (!nodeToCoverWith.isCovered()) {
						if (covers(nodeToCoverWith.getState(), node.getState())) {
							node.setCoveringNode(nodeToCoverWith);
							return;
						}
					}
				}

			}

			for (final ArgNode<XtaState<ItpZoneState>, XtaAction> nodeToCoverWith : candidates) {
				if (node != nodeToCoverWith) {
					if (!nodeToCoverWith.isCovered()) {
						if (couldCover(nodeToCoverWith.getState(), node.getState())) {
							refiner.enforceZone(node, nodeToCoverWith.getState().getState().getInterpolant());
							node.setCoveringNode(nodeToCoverWith);
							return;
						}
					}
				}
			}
		}

		private void expand(final ArgNode<XtaState<ItpZoneState>, XtaAction> v) {
			argBuilder.expand(v, UnitPrec.getInstance());
		}

		private boolean covers(final XtaState<ItpZoneState> state1, final XtaState<ItpZoneState> state2) {
			return state2.getLocs().equals(state1.getLocs()) && state2.getVal().equals(state2.getVal())
					&& state2.getState().getZone().isLeq(state1.getState().getZone());
		}

		private boolean couldCover(final XtaState<ItpZoneState> state1, final XtaState<ItpZoneState> state2) {
			return state2.getLocs().equals(state1.getLocs()) && state2.getVal().equals(state2.getVal())
					&& state2.getState().getZone().isLeq(state1.getState().getInterpolant());
		}

	}

}
