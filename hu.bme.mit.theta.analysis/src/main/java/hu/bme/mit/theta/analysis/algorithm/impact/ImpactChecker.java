package hu.bme.mit.theta.analysis.algorithm.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Optional;
import java.util.function.Predicate;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Analysis;
import hu.bme.mit.theta.analysis.Domain;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgBuilder;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.impact.ImpactRefiner.RefinementResult;

public final class ImpactChecker<S extends State, A extends Action, P extends Precision>
		implements SafetyChecker<S, A, P> {

	private final Analysis<S, A, P> analysis;
	private final ImpactRefiner<S, A> refiner;
	private final Predicate<? super S> target;

	private ImpactChecker(final Analysis<S, A, P> analysis, final ImpactRefiner<S, A> refiner,
			final Predicate<? super S> target) {
		this.analysis = checkNotNull(analysis);
		this.refiner = checkNotNull(refiner);
		this.target = checkNotNull(target);
	}

	public static <S extends State, A extends Action, P extends Precision> ImpactChecker<S, A, P> create(
			final Analysis<S, A, P> analysis, final ImpactRefiner<S, A> refiner, final Predicate<? super S> target) {
		return new ImpactChecker<>(analysis, refiner, target);
	}

	////

	@Override
	public SafetyStatus<S, A> check(final P precision) {
		return new CheckMethod<>(analysis, refiner, target, precision).run();
	}

	////

	private static final class CheckMethod<S extends State, A extends Action, P extends Precision> {
		private final ImpactRefiner<S, A> refiner;
		private final P precision;

		private final Domain<S> domain;
		private final ArgBuilder<S, A, P> argBuilder;
		private final ARG<S, A> arg;

		private CheckMethod(final Analysis<S, A, P> analysis, final ImpactRefiner<S, A> refiner,
				final Predicate<? super S> target, final P precision) {
			this.refiner = refiner;
			this.precision = checkNotNull(precision);
			domain = analysis.getDomain();
			argBuilder = ArgBuilder.create(analysis, target);
			arg = ARG.create(domain);
		}

		private SafetyStatus<S, A> run() {
			final Optional<ArgNode<S, A>> unsafeNode = unwind();

			if (unsafeNode.isPresent()) {
				return SafetyStatus.unsafe(ArgTrace.to(unsafeNode.get()).toTrace(), arg);
			} else {
				return SafetyStatus.safe(arg);
			}
		}

		////

		public void close(final ArgNode<S, A> v) {
			for (final ArgNode<S, A> w : arg.getNodes()) {
				if (w.getId() >= v.getId()) {
					return;
				}

				cover(v, w);
				if (v.getCoveringNode().isPresent()) {
					return;
				}
			}
		}

		private Optional<ArgNode<S, A>> dfs(final ArgNode<S, A> v) {
			close(v);
			if (!v.isCovered()) {
				if (v.isTarget()) {
					final boolean refined = refine(v);
					if (refined) {
						v.ancestors().forEach(w -> close(w));
					} else {
						return Optional.of(v);
					}
				}
				expand(v);
				v.children().forEach(w -> dfs(w));
			}

			return Optional.empty();
		}

		private Optional<ArgNode<S, A>> unwind() {
			argBuilder.init(arg, precision);
			while (true) {
				final Optional<ArgNode<S, A>> uncoveredLeaf = anyUncoveredLeaf();

				if (uncoveredLeaf.isPresent()) {
					final ArgNode<S, A> v = uncoveredLeaf.get();
					v.properAncestors().forEach(w -> close(w));

					final Optional<ArgNode<S, A>> unsafeNode = dfs(v);
					if (unsafeNode.isPresent()) {
						return unsafeNode;
					}
				}

				return Optional.empty();
			}
		}

		////

		private void expand(final ArgNode<S, A> v) {
			if (v.isLeaf() && !v.isCovered()) {
				argBuilder.expand(v, precision);
			}
		}

		private boolean refine(final ArgNode<S, A> v) {
			if (v.isTarget() && !domain.isBottom(v.getState())) {
				final ArgTrace<S, A> argTrace = ArgTrace.to(v);

				final Trace<S, A> trace = argTrace.toTrace();
				final RefinementResult<S, A> refinementResult = refiner.refine(trace);

				if (refinementResult.isSuccesful()) {
					final Trace<S, A> refinedTrace = refinementResult.asSuccesful().getTrace();
					for (int i = 0; i < argTrace.length(); i++) {
						argTrace.node(i).setState(refinedTrace.getState(i));
					}
				} else {
					return false;
				}
			}

			return true;
		}

		private void cover(final ArgNode<S, A> v, final ArgNode<S, A> w) {
			if (!v.isCovered() && !w.ancestors().anyMatch(n -> n == v)) {
				if (domain.isLeq(v.getState(), w.getState())) {
					arg.cover(v, w);
					v.descendants().forEach(y -> y.getCoveredNodes().stream().forEach(x -> arg.uncover(x)));
				}
			}
		}

		////

		private Optional<ArgNode<S, A>> anyUncoveredLeaf() {
			return arg.getLeafNodes().stream().filter(n -> !n.isCovered()).findFirst();
		}

	}

}
