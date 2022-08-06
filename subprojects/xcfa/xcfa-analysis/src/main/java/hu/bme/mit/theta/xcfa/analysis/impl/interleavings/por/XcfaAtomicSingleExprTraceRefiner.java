package hu.bme.mit.theta.xcfa.analysis.impl.interleavings.por;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaState;

/**
 * A Refiner implementation that can refine a single trace (of XcfaStates and XcfaActions) by delegating to a
 * SingleExprTraceChecker. Importantly, when a node is selected to be pruned at the end of the refinement, it is only
 * pruned if the action of its incoming edge is not part of an atomic block. Otherwise, the closest ancestor of the node
 * is pruned for whom the above condition holds.
 */
public final class XcfaAtomicSingleExprTraceRefiner<S extends XcfaState<?>, A extends XcfaAction, P extends Prec, R extends Refutation>
		implements Refiner<S, A, P> {

	private final SingleExprTraceRefiner<S, A, P, R> singleExprTraceRefiner;

	private XcfaAtomicSingleExprTraceRefiner(SingleExprTraceRefiner<S, A, P, R> singleExprTraceRefiner) {
		this.singleExprTraceRefiner = singleExprTraceRefiner;
	}

	public static <S extends XcfaState<?>, A extends XcfaAction, P extends Prec, R extends Refutation> XcfaAtomicSingleExprTraceRefiner<S, A, P, R> create(
			final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
			final PruneStrategy pruneStrategy, final Logger logger) {
		return new XcfaAtomicSingleExprTraceRefiner<>(
				SingleExprTraceRefiner.create(exprTraceChecker, precRefiner, pruneStrategy, logger, new AtomicNodePruner<>())
		);
	}

	@Override
	public RefinerResult<S, A, P> refine(ARG<S, A> arg, P prec) {
		return singleExprTraceRefiner.refine(arg, prec);
	}
}
