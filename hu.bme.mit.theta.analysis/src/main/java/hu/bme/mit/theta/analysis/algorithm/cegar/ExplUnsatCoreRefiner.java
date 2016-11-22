package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.ArgTrace;
import hu.bme.mit.theta.analysis.expl.ExplPrecision;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.analysis.expr.ExprTraceChecker;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus2;
import hu.bme.mit.theta.analysis.expr.UnsatCoreRefutation;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

public class ExplUnsatCoreRefiner<A extends ExprAction> implements Refiner<ExplState, A, ExplPrecision> {

	ExprTraceChecker<UnsatCoreRefutation> exprTraceChecker;

	private ExplUnsatCoreRefiner(final ExprTraceChecker<UnsatCoreRefutation> exprTraceChecker) {
		this.exprTraceChecker = checkNotNull(exprTraceChecker);
	}

	public static <A extends ExprAction> ExplUnsatCoreRefiner<A> create(
			final ExprTraceChecker<UnsatCoreRefutation> exprTraceChecker) {
		return new ExplUnsatCoreRefiner<>(exprTraceChecker);
	}

	@Override
	public RefinerResult<ExplState, A, ExplPrecision> refine(final ARG<ExplState, A> arg,
			final ExplPrecision precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(!arg.isSafe());

		final ArgTrace<ExplState, A> cexToConcretize = arg.getCexs().findFirst().get();
		final Trace<ExplState, A> traceToConcretize = cexToConcretize.toTrace();

		final ExprTraceStatus2<UnsatCoreRefutation> cexStatus = exprTraceChecker.check(traceToConcretize);

		if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(traceToConcretize);
		} else if (cexStatus.isInfeasible()) {
			final UnsatCoreRefutation refutation = cexStatus.asInfeasible().getRefutation();

			final ExplPrecision refinedPrecision = precision.refine(ExprUtils.getVars(refutation.getUnsatCore()));
			final int pruneIndex = refutation.getPruneIndex();
			checkState(0 <= pruneIndex && pruneIndex <= cexToConcretize.length());
			final ArgNode<ExplState, A> nodeToPrune = cexToConcretize.node(pruneIndex);
			arg.prune(nodeToPrune);
			return RefinerResult.spurious(refinedPrecision);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}

}
