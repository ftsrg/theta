package hu.bme.mit.theta.analysis.expr.refinement;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.function.BiFunction;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;

public class ExprTraceCombinedChecker<R extends Refutation> implements ExprTraceChecker<R> {

	public static interface ExprTraceStatusMerger<R extends Refutation>
			extends BiFunction<ExprTraceStatus<R>, ExprTraceStatus<R>, ExprTraceStatus<R>> {
	}

	private final ExprTraceChecker<R> checker1;
	private final ExprTraceChecker<R> checker2;
	private final ExprTraceStatusMerger<R> merger;

	private ExprTraceCombinedChecker(final ExprTraceChecker<R> checker1, final ExprTraceChecker<R> checker2,
			final ExprTraceStatusMerger<R> merger) {
		this.checker1 = checkNotNull(checker1);
		this.checker2 = checkNotNull(checker2);
		this.merger = checkNotNull(merger);
	}

	public static <R extends Refutation> ExprTraceCombinedChecker<R> create(final ExprTraceChecker<R> checker1,
			final ExprTraceChecker<R> checker2, final ExprTraceStatusMerger<R> merger) {
		return new ExprTraceCombinedChecker<>(checker1, checker2, merger);
	}

	@Override
	public ExprTraceStatus<R> check(final Trace<? extends ExprState, ? extends ExprAction> trace) {
		final ExprTraceStatus<R> status1 = checker1.check(trace);
		final ExprTraceStatus<R> status2 = checker2.check(trace);
		return merger.apply(status1, status2);
	}
}
