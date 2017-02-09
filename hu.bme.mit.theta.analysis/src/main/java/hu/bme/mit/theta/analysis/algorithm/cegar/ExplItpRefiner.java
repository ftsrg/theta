package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.function.Function;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public final class ExplItpRefiner<S extends State, A extends ExprAction> implements Refiner<S, A, ExplPrecision> {

	private final ExprTraceChecker<ItpRefutation> exprTraceChecker;
	private final Logger logger;
	private final Function<S, ExplState> mapper;

	private ExplItpRefiner(final ExprTraceChecker<ItpRefutation> exprTraceChecker, final Function<S, ExplState> mapper,
			final Logger logger) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
		this.mapper = mapper;
		this.logger = checkNotNull(logger);
	}

	public static <S extends State, A extends ExprAction> ExplItpRefiner<S, A> create(
			final ExprTraceChecker<ItpRefutation> exprTraceChecker, final Function<S, ExplState> mapper,
			final Logger logger) {
		return new ExplItpRefiner<>(exprTraceChecker, mapper, logger);
	}

	public static <A extends ExprAction> ExplItpRefiner<ExplState, A> create(
			final ExprTraceChecker<ItpRefutation> exprTraceChecker, final Logger logger) {
		return create(exprTraceChecker, s -> s, logger);
	}

	@Override
	public RefinerResult<S, A, ExplPrecision> refine(final ARG<S, A> arg, final ExplPrecision precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<S, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<S, A> traceToConcretize = cexToConcretize.toTrace();
		final Trace<ExplState, A> explStateTrace = traceToConcretize.mapStates(mapper);
		logger.writeln("Trace length: ", traceToConcretize.length(), 3, 2);
		logger.writeln("Trace: ", traceToConcretize, 4, 3);

		logger.write("Checking...", 3, 2);
		final ExprTraceStatus<ItpRefutation> cexStatus = exprTraceChecker.check(explStateTrace);
		logger.writeln("done: ", cexStatus, 3, 0);

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else if (cexStatus.isInfeasible()) {
			final ItpRefutation interpolant = cexStatus.asInfeasible().getRefutation();
			logger.writeln(interpolant, 4, 3);

			final ExplPrecision refinedPrecision = precision.refine(ExprUtils.getVars(interpolant));
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
