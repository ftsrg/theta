package hu.bme.mit.theta.xcfa.analysis.impl.interleavings.por;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.Refiner;
import hu.bme.mit.theta.analysis.algorithm.cegar.RefinerResult;
import hu.bme.mit.theta.analysis.expr.refinement.*;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaAction;
import hu.bme.mit.theta.xcfa.analysis.impl.interleavings.XcfaState;

public final class XcfaAtomicMultiExprTraceRefiner<S extends XcfaState<?>, A extends XcfaAction, P extends Prec, R extends Refutation>
		implements Refiner<S, A, P> {

	private final MultiExprTraceRefiner<S, A, P, R> multiExprTraceRefiner;

	private XcfaAtomicMultiExprTraceRefiner(MultiExprTraceRefiner<S, A, P, R> multiExprTraceRefiner) {
		this.multiExprTraceRefiner = multiExprTraceRefiner;
	}

	public static <S extends XcfaState<?>, A extends XcfaAction, P extends Prec, R extends Refutation> XcfaAtomicMultiExprTraceRefiner<S, A, P, R> create(
			final ExprTraceChecker<R> exprTraceChecker, final PrecRefiner<S, A, P, R> precRefiner,
			final PruneStrategy pruneStrategy, final Logger logger) {
		return new XcfaAtomicMultiExprTraceRefiner<>(
				MultiExprTraceRefiner.create(exprTraceChecker, precRefiner, pruneStrategy, logger, new AtomicNodePruner<>())
		);
	}

	@Override
	public RefinerResult<S, A, P> refine(ARG<S, A> arg, P prec) {
		return multiExprTraceRefiner.refine(arg, prec);
	}
}
