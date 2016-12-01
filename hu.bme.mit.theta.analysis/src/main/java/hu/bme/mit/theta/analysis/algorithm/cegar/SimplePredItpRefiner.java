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
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus;
import hu.bme.mit.theta.analysis.expr.ItpRefutation;
import hu.bme.mit.theta.analysis.pred.PredState;
import hu.bme.mit.theta.analysis.pred.SimplePredPrecision;
import hu.bme.mit.theta.core.expr.BoolLitExpr;

public final class SimplePredItpRefiner<A extends ExprAction> implements Refiner<PredState, A, SimplePredPrecision> {

	ExprTraceChecker<ItpRefutation> exprTraceChecker;

	private SimplePredItpRefiner(final ExprTraceChecker<ItpRefutation> exprTraceChecker) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
	}

	public static <A extends ExprAction> SimplePredItpRefiner<A> create(
			final ExprTraceChecker<ItpRefutation> exprTraceChecker) {
		return new SimplePredItpRefiner<>(exprTraceChecker);
	}

	@Override
	public RefinerResult<PredState, A, SimplePredPrecision> refine(final ARG<PredState, A> arg,
			final SimplePredPrecision precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<PredState, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<PredState, A> traceToConcretize = cexToConcretize.toTrace();

		final ExprTraceStatus<ItpRefutation> cexStatus = exprTraceChecker.check(traceToConcretize);

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else if (cexStatus.isInfeasible()) {
			final ItpRefutation interpolant = cexStatus.asInfeasible().getRefutation();
			final SimplePredPrecision refinedPrecision = precision
					.refine(interpolant.stream().filter(p -> !(p instanceof BoolLitExpr)).collect(Collectors.toSet()));
			final int pruneIndex = interpolant.getPruneIndex();
			checkState(0 <= pruneIndex && pruneIndex <= cexToConcretize.length());
			final ArgNode<PredState, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrecision);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}

}
