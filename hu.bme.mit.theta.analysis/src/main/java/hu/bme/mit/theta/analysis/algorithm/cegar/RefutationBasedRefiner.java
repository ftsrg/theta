package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public class RefutationBasedRefiner<S extends State, CS extends State, R extends Refutation, P extends Precision, A extends Action>
		implements Refiner<S, A, P, CS> {

	private final ConcretizerOp<? super S, A, CS, R> concretizerOp;
	private final RefinerOp<S, A, R, P> refinerOp;

	private Trace<S, A> cex;
	private P refinedPrecision;

	public RefutationBasedRefiner(final ConcretizerOp<? super S, A, CS, R> concretizerOp,
			final RefinerOp<S, A, R, P> refinerOp) {
		this.concretizerOp = checkNotNull(concretizerOp);
		this.refinerOp = checkNotNull(refinerOp);
		this.cex = null;
		this.refinedPrecision = null;
	}

	@Override
	public void refine(final ARG<S, A> arg, final P precision) {
		checkArgument(arg.getTargetNodes().size() > 0);

		refinedPrecision = null;

		final Trace<S, A> cexToConcretize = arg.getAnyCex().get();

		concretizerOp.concretize(cexToConcretize);

		if (concretizerOp.getStatus() == CexStatus.SPURIOUS) {
			refinedPrecision = refinerOp.refine(precision, concretizerOp.getRefutation(), cexToConcretize);
		} else {
			cex = cexToConcretize;
		}
	}

	@Override
	public CexStatus getStatus() {
		return concretizerOp.getStatus();
	}

	@Override
	public Trace<S, A> getCex() {
		checkState(concretizerOp.getStatus() == CexStatus.CONCRETE);
		assert (cex != null);
		return cex;
	}

	@Override
	public P getRefinedPrecision() {
		checkState(concretizerOp.getStatus() == CexStatus.SPURIOUS);
		assert (refinedPrecision != null);
		return refinedPrecision;
	}

}
