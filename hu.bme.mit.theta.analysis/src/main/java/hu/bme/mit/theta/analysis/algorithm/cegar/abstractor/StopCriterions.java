package hu.bme.mit.theta.analysis.algorithm.cegar.abstractor;

import static com.google.common.base.Preconditions.checkArgument;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.common.ObjectUtils;

public final class StopCriterions {

	public static <S extends State, A extends Action> StopCriterion<S, A> firstCex() {
		return new FirstCex<>();
	}

	public static <S extends State, A extends Action> StopCriterion<S, A> fullExploration() {
		return new FullExploration<>();
	}

	public static <S extends State, A extends Action> StopCriterion<S, A> atLeastNCexs(final int n) {
		return new AtLeastNCexs<>(n);
	}

	private static final class FirstCex<S extends State, A extends Action> implements StopCriterion<S, A> {
		@Override
		public boolean canStop(final ARG<S, A> arg) {
			return arg.getUnsafeNodes().findAny().isPresent();
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(StopCriterion.class.getSimpleName()).add(getClass().getSimpleName())
					.toString();
		}
	}

	private static final class FullExploration<S extends State, A extends Action> implements StopCriterion<S, A> {
		@Override
		public boolean canStop(final ARG<S, A> arg) {
			return false;
		}

		@Override
		public String toString() {
			return ObjectUtils.toStringBuilder(StopCriterion.class.getSimpleName()).add(getClass().getSimpleName())
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
		public String toString() {
			return ObjectUtils.toStringBuilder(StopCriterion.class.getSimpleName()).add(getClass().getSimpleName())
					.add("N = " + n).toString();
		}
	}
}
