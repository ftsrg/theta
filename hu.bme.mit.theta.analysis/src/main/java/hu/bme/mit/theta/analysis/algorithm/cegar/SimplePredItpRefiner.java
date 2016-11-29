package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus2;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.BoolLitExpr;

public final class SimplePredItpRefiner<A extends ExprAction> implements Refiner<PredState, A, SimplePredPrecision> {

	private final ExprTraceChecker<ItpRefutation> exprTraceChecker;
	private final Logger logger;

	private SimplePredItpRefiner(final ExprTraceChecker<ItpRefutation> exprTraceChecker, final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.logger = checkNotNull(logger);
	}

	public static <A extends ExprAction> SimplePredItpRefiner<A> create(
			final ExprTraceChecker<ItpRefutation> exprTraceChecker, final Logger logger) {
		return new SimplePredItpRefiner<>(exprTraceChecker, logger);
	}

	@Override
	public RefinerResult<PredState, A, SimplePredPrecision> refine(final ARG<PredState, A> arg,
			final SimplePredPrecision precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<PredState, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<PredState, A> traceToConcretize = cexToConcretize.toTrace();
		logger.writeln("Trace length: ", traceToConcretize.length(), 3, 2);
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		logger.write("Checking...", 3, 2);
		final ExprTraceStatus2<ItpRefutation> cexStatus = exprTraceChecker.check(traceToConcretize);
		logger.writeln("done: ", cexStatus, 3, 0);

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else if (cexStatus.isInfeasible()) {
			final ItpRefutation interpolant = cexStatus.asInfeasible().getRefutation();
			logger.writeln(interpolant, 4, 3);
			final SimplePredPrecision refinedPrecision = precision
					.refine(interpolant.stream().filter(p -> !(p instanceof BoolLitExpr)).collect(Collectors.toSet()));
			final int pruneIndex = interpolant.getPruneIndex();
			checkState(0 <= pruneIndex && pruneIndex <= cexToConcretize.length());
			logger.writeln("Pruning from index ", pruneIndex, 3, 2);
			final ArgNode<PredState, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrecision);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}

}
