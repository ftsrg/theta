package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.Trace;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.AbstractorStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CEGARLoop;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CEGARStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CounterexampleStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Refiner;

public class CEGARLoopImpl<S extends State, A extends Action, P extends Precision, CS extends State>
		implements CEGARLoop<P, CS, A> {

	private final Abstractor<S, A, ? super P> abstractor;
	private final Refiner<S, A, P, CS> refiner;

	public CEGARLoopImpl(final Abstractor<S, A, ? super P> abstractor, final Refiner<S, A, P, CS> refiner) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
	}

	@Override
	public CEGARStatus check(final P initPrecision) {

		P precision = initPrecision;
		do {

			abstractor.init(precision); // TODO: currently the ARG is not
										// pruned, so the abstractor simply
										// restarts at every iteration
			abstractor.check(precision);

			if (abstractor.getStatus() == AbstractorStatus.COUNTEREXAMPLE) {
				final ARG<S, A, ? super P> arg = abstractor.getARG();
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
	public CEGARStatus getStatus() {
		if (abstractor.getStatus() == AbstractorStatus.OK) {
			return CEGARStatus.OK;
		} else if (refiner.getStatus() == CounterexampleStatus.CONCRETE) {
			return CEGARStatus.COUNTEREXAMPLE;
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
