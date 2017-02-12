package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.common.logging.Logger;

public class SingleExprTraceRefiner<S extends ExprState, A extends ExprAction, P extends Precision, R extends Refutation>
		implements Refiner<S, A, P> {

	private final ExprTraceChecker<R> exprTraceChecker;
	private final TraceRefiner<S, A, P, R> traceRefiner;
	private final Logger logger;

	private SingleExprTraceRefiner(final ExprTraceChecker<R> exprTraceChecker,
			final TraceRefiner<S, A, P, R> traceRefiner, final Logger logger) {
		this.exprTraceChecker = exprTraceChecker;
		this.traceRefiner = traceRefiner;
		this.logger = logger;
	}

	public static <S extends ExprState, A extends ExprAction, P extends Precision, R extends Refutation> SingleExprTraceRefiner<S, A, P, R> create(
			final ExprTraceChecker<R> exprTraceChecker, final TraceRefiner<S, A, P, R> traceRefiner,
			final Logger logger) {
		return new SingleExprTraceRefiner<>(exprTraceChecker, traceRefiner, logger);
	}

	@Override
	public RefinerResult<S, A, P> refine(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<S, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<S, A> traceToConcretize = cexToConcretize.toTrace();
		logger.writeln("Trace length: ", traceToConcretize.length(), 3, 2);
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		logger.write("Checking...", 3, 2);
		final ExprTraceStatus<R> cexStatus = exprTraceChecker.check(traceToConcretize);
		logger.writeln("done: ", cexStatus, 3, 0);

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else if (cexStatus.isInfeasible()) {
			final R refutation = cexStatus.asInfeasible().getRefutation();
			logger.writeln(refutation, 4, 3);
			final P refinedPrecision = traceRefiner.refine(traceToConcretize, precision, refutation);
			final int pruneIndex = refutation.getPruneIndex();
			checkState(0 <= pruneIndex && pruneIndex <= cexToConcretize.length());
			logger.writeln("Pruning from index ", pruneIndex, 3, 2);
			final ArgNode<S, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrecision);
		}
		throw new IllegalStateException("Unknown status.");
	}

}
