package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.expr.refinement.ExprTraceCombinedChecker.ExprTraceStatusMerger;

public final class ExprTraceStatusMergers {

	private ExprTraceStatusMergers() {
	}

	public static <R extends Refutation> ExprTraceStatusMerger<R> minPruneIndex() {
		return new MinPruneIndex<>();
	}

	public static <R extends Refutation> ExprTraceStatusMerger<R> maxPruneIndex() {
		return new MaxPruneIndex<>();
	}

	private static class MinPruneIndex<R extends Refutation> implements ExprTraceStatusMerger<R> {
		@Override
		public ExprTraceStatus<R> apply(final ExprTraceStatus<R> status1, final ExprTraceStatus<R> status2) {
			checkState(status1.isFeasible() == status2.isFeasible(), "Checkers disagree on trace status");

			if (status1.isFeasible()) {
				return status1;
			}

			assert status1.isInfeasible() && status2.isInfeasible();
			final int pruneIndex1 = status1.asInfeasible().getRefutation().getPruneIndex();
			final int pruneIndex2 = status2.asInfeasible().getRefutation().getPruneIndex();

			if (pruneIndex1 < pruneIndex2) {
				return status1;
			} else {
				return status2;
			}
		}
	}

	private static class MaxPruneIndex<R extends Refutation> implements ExprTraceStatusMerger<R> {
		@Override
		public ExprTraceStatus<R> apply(final ExprTraceStatus<R> status1, final ExprTraceStatus<R> status2) {
			checkState(status1.isFeasible() == status2.isFeasible(), "Checkers disagree on trace status");

			if (status1.isFeasible()) {
				return status1;
			}

			assert status1.isInfeasible() && status2.isInfeasible();
			final int pruneIndex1 = status1.asInfeasible().getRefutation().getPruneIndex();
			final int pruneIndex2 = status2.asInfeasible().getRefutation().getPruneIndex();

			if (pruneIndex1 > pruneIndex2) {
				return status1;
			} else {
				return status2;
			}
		}
	}
}
