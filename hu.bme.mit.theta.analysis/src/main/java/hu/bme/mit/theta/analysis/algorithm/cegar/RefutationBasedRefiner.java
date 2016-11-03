package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;

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
	public RefinerStatus<S, A, P> refine(final ARG<S, A> arg, final P precision) {
		checkArgument(arg.getTargetNodes().size() > 0);

		final Trace<S, A> cexToConcretize = arg.getAnyCex().get().toTrace();

		final CexStatus<R> cexStatus = concretizerOp.checkConcretizable(cexToConcretize);

		if (cexStatus.isSpurious()) {
			final R refutation = cexStatus.asSpurious().getRefutation();
			final P refinedPrecision = refinerOp.refine(precision, refutation, cexToConcretize);
			return RefinerStatus.spurious(arg, refinedPrecision);
		} else if (cexStatus.isConcretizable()) {
			return RefinerStatus.concretizable(arg, cexToConcretize);
		} else {
			throw new IllegalStateException("Unknown status.");
		}
	}
}
