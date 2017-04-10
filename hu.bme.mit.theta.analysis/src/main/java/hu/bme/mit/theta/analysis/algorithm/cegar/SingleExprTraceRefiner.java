package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.Refutation;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.logging.Logger;

public class SingleExprTraceRefiner<S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation>
		implements Refiner<S, A, P> {

	private final ExprTraceChecker<R> exprTraceChecker;
	private final PrecRefiner<S, A, P, R> precRefiner;
	private final Logger logger;

	private SingleExprTraceRefiner(final ExprTraceChecker<R> exprTraceChecker,
			final PrecRefiner<S, A, P, R> precRefiner, final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.precRefiner = checkNotNull(precRefiner);
		this.logger = checkNotNull(logger);
	}

	public static <S extends ExprState, A extends ExprAction, P extends Prec, R extends Refutation> SingleExprTraceRefiner<S, A, P, R> create(
			final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
			final Logger logger) {
		return new SingleExprTraceRefiner<>(exprTraceChecker, precRefiner, logger);
	}

	@Override
	public RefinerResult<S, A, P> refine(final ARG<S, A> arg, final P prec) {
		checkNotNull(arg);
		checkNotNull(prec);
		checkArgument(!arg.isSafe(), "ARG must be unsafe");

		final ArgTrace<S, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<S, A> traceToConcretize = cexToConcretize.toTrace();
		logger.writeln("Trace length: ", traceToConcretize.length(), 3, 2);
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		logger.write("Checking...", 3, 2);
		final ExprTraceStatus<R> cexStatus = exprTraceChecker.check(traceToConcretize);
		logger.writeln("done: ", cexStatus, 3, 0);

		checkState(cexStatus.isFeasible() || cexStatus.isInfeasible(), "Unknown status.");

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else {
			final R refutation = cexStatus.asInfeasible().getRefutation();
			logger.writeln(refutation, 4, 3);
			final P refinedPrec = precRefiner.refine(traceToConcretize, prec, refutation);
			checkState(!refinedPrec.equals(prec), "Precision is not refined");
			final int pruneIndex = refutation.getPruneIndex();
			checkState(0 <= pruneIndex && pruneIndex <= cexToConcretize.length(), "Pruning index out of range");
			logger.writeln("Pruning from index ", pruneIndex, 3, 2);
			final ArgNode<S, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrec);
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(exprTraceChecker).add(precRefiner)
				.toString();
	}

}
