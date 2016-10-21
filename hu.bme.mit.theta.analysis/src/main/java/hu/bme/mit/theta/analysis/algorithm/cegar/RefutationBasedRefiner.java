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

	private Trace<S, A> cex;
	private P refinedPrecision;
	private ARG<S, A> arg;

	public RefutationBasedRefiner(final ConcretizerOp<? super S, A, R> concretizerOp,
			final RefinerOp<S, A, R, P> refinerOp) {
		this.concretizerOp = checkNotNull(concretizerOp);
		this.refinerOp = checkNotNull(refinerOp);
		this.cex = null;
		this.refinedPrecision = null;
		this.arg = null;
	}

	@Override
	public void refine(final ARG<S, A> arg, final P precision) {
		checkArgument(arg.getTargetNodes().size() > 0);

		refinedPrecision = null;
		this.arg = arg;

		final Trace<S, A> cexToConcretize = arg.getAnyCex().get();

		concretizerOp.concretize(cexToConcretize);

		if (concretizerOp.getStatus() == CexStatus.SPURIOUS) {
			refinedPrecision = refinerOp.refine(precision, concretizerOp.getRefutation(), cexToConcretize);
		} else {
			cex = cexToConcretize;
		}
	}

	@Override
	public RefinerStatus<S, A, P> getStatus() {

		switch (concretizerOp.getStatus()) {
		case CONCRETE:
			assert cex != null;
			return RefinerStatus.concretizable(cex);
		case SPURIOUS:
			assert refinedPrecision != null;
			assert arg != null;
			return RefinerStatus.spurious(arg, refinedPrecision);
		default:
			throw new IllegalStateException();
		}
	}

}
