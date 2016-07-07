package hu.bme.mit.inf.ttmc.analysis.algorithm.impl;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.inf.ttmc.analysis.Action;
import hu.bme.mit.inf.ttmc.analysis.Counterexample;
import hu.bme.mit.inf.ttmc.analysis.Precision;
import hu.bme.mit.inf.ttmc.analysis.State;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Abstractor;
import hu.bme.mit.inf.ttmc.analysis.algorithm.AbstractorStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CEGARLoop;
import hu.bme.mit.inf.ttmc.analysis.algorithm.CEGARStatus;
import hu.bme.mit.inf.ttmc.analysis.algorithm.Refiner;
import hu.bme.mit.inf.ttmc.analysis.algorithm.RefinerStatus;
import hu.bme.mit.inf.ttmc.analysis.expl.ExplState;

public class CEGARLoopImpl<S extends State, A extends Action, P extends Precision> implements CEGARLoop<P> {

	private final Abstractor<S, A, P> abstractor;
	private final Refiner<S, A, P> refiner;

	private CEGARLoopImpl(final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
	}

	@Override
	public CEGARStatus check(final P initPrecision) {

		P precision = initPrecision;
		do {
			abstractor.init(precision); // TODO: currently the ARG is not pruned, so the abstractor simply restarts at every iteration
			abstractor.check(precision);

			if (abstractor.getStatus() == AbstractorStatus.Counterexample) {
				final ARG<S, A> arg = abstractor.getARG();
				refiner.refine(arg);

				if (refiner.getStatus() == RefinerStatus.Spurious) {
					precision = refiner.getRefinedPrecision();
				}
			}

		} while (!(abstractor.getStatus() == AbstractorStatus.Ok) && !(refiner.getStatus() == RefinerStatus.Concrete));

		return getStatus();
	}

	@Override
	public CEGARStatus getStatus() {
		if (abstractor.getStatus() == AbstractorStatus.Ok) {
			return CEGARStatus.Ok;
		} else if (refiner.getStatus() == RefinerStatus.Concrete) {
			return CEGARStatus.Counterexample;
		} else {
			throw new IllegalStateException();
		}
	}

	@Override
	public Counterexample<ExplState> getCounterexample() {
		checkState(refiner.getStatus() == RefinerStatus.Concrete);
		return refiner.getConcreteCounterexample();
	}
}
