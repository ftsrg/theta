package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.Collection;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CounterexampleStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Refiner;
import hu.bme.mit.inf.ttmc.analysis.refutation.Refutation;

public class RefutationBasedRefiner<S extends State, CS extends State, R extends Refutation, P extends Precision, A extends Action>
		implements Refiner<S, A, P, CS> {

	private final ConcretizerOp<? super S, A, CS, R> concretizerOp;
	private final RefinerOp<S, A, R, P> refinerOp;

	private P refinedPrecision;

	public RefutationBasedRefiner(final ConcretizerOp<? super S, A, CS, R> concretizerOp, final RefinerOp<S, A, R, P> refinerOp) {
		this.concretizerOp = checkNotNull(concretizerOp);
		this.refinerOp = checkNotNull(refinerOp);
		this.refinedPrecision = null;
	}

	@Override
	public CounterexampleStatus refine(final ARG<S, A> arg, final P precision) {
		checkArgument(arg.getTargetNodes().size() > 0);

		refinedPrecision = null;

		final Collection<Counterexample<S, A>> counterexamples = arg.getCounterexamples();
		assert (counterexamples.size() == 1); // TODO: currently this refiner only considers one counterexample

		final Counterexample<S, A> counterexample = counterexamples.iterator().next();

		concretizerOp.concretize(counterexample);

		if (concretizerOp.getStatus() == CounterexampleStatus.Spurious) {
			refinedPrecision = refinerOp.refine(precision, concretizerOp.getRefutation(), counterexample);
		}

		return getStatus();
	}

	@Override
	public CounterexampleStatus getStatus() {
		return concretizerOp.getStatus();
	}

	@Override
	public Counterexample<CS, A> getConcreteCounterexample() {
		checkState(concretizerOp.getStatus() == CounterexampleStatus.Concrete);
		return concretizerOp.getConcreteCounterexample();
	}

	@Override
	public P getRefinedPrecision() {
		checkState(concretizerOp.getStatus() == CounterexampleStatus.Spurious);
		assert (refinedPrecision != null);
		return refinedPrecision;
	}

}
