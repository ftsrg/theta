package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;

public class ExprTraceCombinedChecker<R extends Refutation> implements ExprTraceChecker<R> {

	private final Collection<ExprTraceChecker<R>> checkers;
	private final ExprTraceStatusMerger<R> merger;

	private ExprTraceCombinedChecker(final Collection<ExprTraceChecker<R>> checkers,
			final ExprTraceStatusMerger<R> merger) {
		this.checkers = ImmutableList.copyOf(checkNotNull(checkers));
		this.merger = checkNotNull(merger);
	}

	public static <R extends Refutation> ExprTraceCombinedChecker<R> create(final ExprTraceChecker<R> checker1,
			final ExprTraceChecker<R> checker2, final ExprTraceStatusMerger<R> merger) {
		return new ExprTraceCombinedChecker<>(ImmutableList.of(checker1, checker2), merger);
	}

	@Override
	public ExprTraceStatus<R> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		final List<ExprTraceStatus<R>> statuses = checkers.stream().map(c -> c.check(trace))
				.collect(Collectors.toList());
		return merger.merge(statuses);
	}
}
