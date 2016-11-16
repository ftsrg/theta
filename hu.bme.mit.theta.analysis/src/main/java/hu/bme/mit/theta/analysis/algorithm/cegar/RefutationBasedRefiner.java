package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.expr.ExprTraceStatus2;
import hu.bme.mit.theta.analysis.expr.Refutation;

public class RefutationBasedRefiner<S extends State, A extends Action, P extends Precision, R extends Refutation>
		implements Refiner<S, A, P> {

	private final ConcretizerOp<? super S, A, R> concretizerOp;
	private final RefinerOp<S, A, R, P> refinerOp;

	public RefutationBasedRefiner(final ConcretizerOp<? super S, A, R> concretizerOp,
			final RefinerOp<S, A, R, P> refinerOp) {
		this.concretizerOp = checkNotNull(concretizerOp);
		this.refinerOp = checkNotNull(refinerOp);
	}

	@Override
	public RefinerResult<S, A, P> refine(final ARG<S, A> arg, final P precision) {
		checkNotNull(arg);
		checkNotNull(precision);
		checkArgument(arg.getUnsafeNodes().findFirst().isPresent());

		final Trace<S, A> cexToConcretize = arg.getCexs().findFirst().get().toTrace();

		final ExprTraceStatus2<R> cexStatus = concretizerOp.checkConcretizable(cexToConcretize);

		if (cexStatus.isInfeasible()) {
			final R refutation = cexStatus.asInfeasible().getRefutation();
			final P refinedPrecision = refinerOp.refine(precision, refutation, cexToConcretize);
			// TODO: prune ARG
			return RefinerResult.spurious(refinedPrecision);
		} else if (cexStatus.isFeasible()) {
			return RefinerResult.unsafe(cexToConcretize);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}
}
