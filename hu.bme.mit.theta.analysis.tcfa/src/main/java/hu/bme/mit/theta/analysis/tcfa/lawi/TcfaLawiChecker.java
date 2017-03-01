package hu.bme.mit.theta.analysis.tcfa.lawi;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
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
import hu.bme.mit.theta.analysis.impl.NullPrec;
import hu.bme.mit.theta.analysis.reachedset.Partition;
import hu.bme.mit.theta.analysis.tcfa.TcfaAction;
import hu.bme.mit.theta.analysis.waitlist.PriorityWaitlist;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.formalism.tcfa.TCFA;
import hu.bme.mit.theta.formalism.tcfa.TcfaLoc;
import hu.bme.mit.theta.solver.Solver;

public final class TcfaLawiChecker implements SafetyChecker<TcfaLawiState, TcfaAction, NullPrec> {
	private final TCFA tcfa;
	private final ArgBuilder<TcfaLawiState, TcfaAction, NullPrec> argBuilder;

	private TcfaLawiChecker(final TCFA tcfa, final Predicate<? super TcfaLoc> errorLocs, final Solver solver) {
		checkNotNull(errorLocs);
		checkNotNull(solver);

		this.tcfa = checkNotNull(tcfa);

		final LTS<TcfaLawiState, TcfaAction> lts = TcfaLawiLts.create(tcfa);
		final Analysis<TcfaLawiState, TcfaAction, NullPrec> analysis = TcfaLawiAnalysis.create(tcfa, solver);
		final Predicate<TcfaLawiState> target = s -> errorLocs.test(s.getLoc());

		argBuilder = ArgBuilder.create(lts, analysis, target);
	}

	public static TcfaLawiChecker create(final TCFA tcfa, final Predicate<? super TcfaLoc> errorLocs,
			final Solver solver) {
		return new TcfaLawiChecker(tcfa, errorLocs, solver);
	}

	@Override
	public SafetyResult<TcfaLawiState, TcfaAction> check(final NullPrec prec) {
		return new CheckMethod().run();
	}

	private final class CheckMethod {
		private final ARG<TcfaLawiState, TcfaAction> arg;
		private final Waitlist<ArgNode<TcfaLawiState, TcfaAction>> waitlist;
		private final Partition<ArgNode<TcfaLawiState, TcfaAction>, TcfaLoc> reachedSet;
		private final TcfaLawiRefiner refiner;

		private CheckMethod() {
			waitlist = PriorityWaitlist.create(ArgNodeComparators.bfs());
			reachedSet = Partition.of(n -> n.getState().getLoc());
			refiner = TcfaLawiRefiner.create(tcfa, waitlist);
			arg = argBuilder.createArg();

			argBuilder.init(arg, NullPrec.getInstance());
			waitlist.addAll(arg.getInitNodes());
			reachedSet.addAll(arg.getInitNodes());
		}

		public SafetyResult<TcfaLawiState, TcfaAction> run() {
			final Optional<ArgNode<TcfaLawiState, TcfaAction>> unsafeNode = searchForUnsafeNode();
			if (unsafeNode.isPresent()) {
				final ArgTrace<TcfaLawiState, TcfaAction> argTrace = ArgTrace.to(unsafeNode.get());
				final Trace<TcfaLawiState, TcfaAction> trace = argTrace.toTrace();
				return SafetyResult.unsafe(trace, arg);
			} else {
				return SafetyResult.safe(arg);
			}
		}

		private Optional<ArgNode<TcfaLawiState, TcfaAction>> searchForUnsafeNode() {
			while (!waitlist.isEmpty()) {
				final ArgNode<TcfaLawiState, TcfaAction> v = waitlist.remove();
				assert v.isLeaf();

				final ZoneState concreteZone = v.getState().getConcreteZone();

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

		private void close(final ArgNode<TcfaLawiState, TcfaAction> node) {
			assert node.isLeaf();

			final Collection<ArgNode<TcfaLawiState, TcfaAction>> candidates = reachedSet.get(node);

			for (final ArgNode<TcfaLawiState, TcfaAction> nodeToCoverWith : candidates) {
				if (node != nodeToCoverWith) {
					if (!nodeToCoverWith.isCovered()) {
						if (covers(nodeToCoverWith.getState(), node.getState())) {
							node.cover(nodeToCoverWith);
							return;
						}
					}
				}

			}

			for (final ArgNode<TcfaLawiState, TcfaAction> nodeToCoverWith : candidates) {
				if (node != nodeToCoverWith) {
					if (!nodeToCoverWith.isCovered()) {
						if (couldCover(nodeToCoverWith.getState(), node.getState())) {
							refiner.enforceZone(node, nodeToCoverWith.getState().getAbstractZone());
							node.cover(nodeToCoverWith);
							return;
						}
					}
				}
			}
		}

		private void expand(final ArgNode<TcfaLawiState, TcfaAction> v) {
			argBuilder.expand(v, NullPrec.getInstance());
		}

		private boolean covers(final TcfaLawiState state1, final TcfaLawiState state2) {
			return state2.getLoc().equals(state1.getLoc()) && state2.getExplState().isLeq(state1.getExplState())
					&& state2.getAbstractZone().isLeq(state1.getAbstractZone());
		}

		private boolean couldCover(final TcfaLawiState state1, final TcfaLawiState state2) {
			return state2.getLoc().equals(state1.getLoc()) && state2.getExplState().isLeq(state1.getExplState())
					&& state2.getConcreteZone().isLeq(state1.getAbstractZone());
		}

	}

}
