package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.function.Function;
import java.util.stream.Collectors;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.expr.BoolLitExpr;

public final class SimplePredItpRefiner<S extends State, A extends ExprAction>
		implements Refiner<S, A, SimplePredPrecision> {

	private final ExprTraceChecker<ItpRefutation> exprTraceChecker;
	private final Logger logger;
	private final Function<S, PredState> mapper;

	private SimplePredItpRefiner(final ExprTraceChecker<ItpRefutation> exprTraceChecker,
			final Function<S, PredState> mapper, final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.mapper = checkNotNull(mapper);
		this.logger = checkNotNull(logger);
	}

	public static <S extends State, A extends ExprAction> SimplePredItpRefiner<S, A> create(
			final ExprTraceChecker<ItpRefutation> exprTraceChecker, final Function<S, PredState> mapper,
			final Logger logger) {
		return new SimplePredItpRefiner<>(exprTraceChecker, mapper, logger);
	}

	public static <A extends ExprAction> SimplePredItpRefiner<PredState, A> create(
			final ExprTraceChecker<ItpRefutation> exprTraceChecker, final Logger logger) {
		return create(exprTraceChecker, s -> s, logger);
	}

	@Override
	public RefinerResult<S, A, SimplePredPrecision> refine(final ARG<S, A> arg, final SimplePredPrecision precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<S, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<S, A> traceToConcretize = cexToConcretize.toTrace();
		final Trace<PredState, A> predStateTrace = traceToConcretize.mapStates(mapper);
		logger.writeln("Trace length: ", traceToConcretize.length(), 3, 2);
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		logger.write("Checking...", 3, 2);
		final ExprTraceStatus<ItpRefutation> cexStatus = exprTraceChecker.check(predStateTrace);
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
			final ArgNode<S, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrecision);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}

	@Override
	public String toString() {
		return ObjectUtils.toStringBuilder(getClass().getSimpleName()).add(exprTraceChecker).toString();
	}
}
