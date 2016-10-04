package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public class CegarLoopImpl<S extends State, A extends Action, P extends Precision, CS extends State>
		implements CegarLoop<P, CS, A> {

	private final Abstractor<S, A, ? super P> abstractor;
	private final Refiner<S, A, P, CS> refiner;

	public CegarLoopImpl(final Abstractor<S, A, ? super P> abstractor, final Refiner<S, A, P, CS> refiner) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
	}

	@Override
	public CegarStatus check(final P initPrecision) {

		P precision = initPrecision;
		do {

			abstractor.init(precision); // TODO: currently the ARG is not
										// pruned, so the abstractor simply
										// restarts at every iteration
			abstractor.check(precision);

			if (abstractor.getStatus() == AbstractorStatus.COUNTEREXAMPLE) {
				final ARG<S, A> arg = abstractor.getARG();
				refiner.refine(arg, precision);

				if (refiner.getStatus() == CounterexampleStatus.SPURIOUS) {
					precision = refiner.getRefinedPrecision();
				}
			}

		} while (!(abstractor.getStatus() == AbstractorStatus.OK)
				&& !(refiner.getStatus() == CounterexampleStatus.CONCRETE));

		return getStatus();
	}

	@Override
	public CegarStatus getStatus() {
		if (abstractor.getStatus() == AbstractorStatus.OK) {
			return CegarStatus.OK;
		} else if (refiner.getStatus() == CounterexampleStatus.CONCRETE) {
			return CegarStatus.COUNTEREXAMPLE;
		} else {
			throw new IllegalStateException();
		}
	}

	@Override
	public Trace<CS, A> getCounterexample() {
		checkState(refiner.getStatus() == CounterexampleStatus.CONCRETE);
		return refiner.getConcreteCounterexample();
	}
}
