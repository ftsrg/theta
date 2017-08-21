package hu.bme.mit.theta.analysis.expr.refinement;

import java.util.Collection;

import com.google.common.collect.ImmutableList;

public interface ExprTraceStatusMerger<R extends Refutation> {
	default ExprTraceStatus<R> merge(final ExprTraceStatus<R> status1, final ExprTraceStatus<R> status2) {
		return merge(ImmutableList.of(status1, status2));
	}

	ExprTraceStatus<R> merge(Collection<ExprTraceStatus<R>> statuses);
}
