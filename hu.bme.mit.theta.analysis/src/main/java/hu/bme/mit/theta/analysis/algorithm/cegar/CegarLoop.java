package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.ARG;

public class CegarLoop<S extends State, A extends Action, P extends Precision, CS extends State> {

	private final Abstractor<S, A, ? super P> abstractor;
	private final Refiner<S, A, P, CS> refiner;

	public CegarLoop(final Abstractor<S, A, ? super P> abstractor, final Refiner<S, A, P, CS> refiner) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
	}

	public CegarStatus check(final P initPrecision) {

		P precision = initPrecision;
		do {

			abstractor.init(precision); // TODO: currently the ARG is not
										// pruned, so the abstractor simply
										// restarts at every iteration
			abstractor.check(precision);

			if (abstractor.getStatus() == AbstractorStatus.CEX) {
				final ARG<S, A> arg = abstractor.getARG();
				refiner.refine(arg, precision);

				if (refiner.getStatus() == CexStatus.SPURIOUS) {
					precision = refiner.getRefinedPrecision();
				}
			}

		} while (!(abstractor.getStatus() == AbstractorStatus.OK) && !(refiner.getStatus() == CexStatus.CONCRETE));

		return getStatus();
	}

	public CegarStatus getStatus() {
		if (abstractor.getStatus() == AbstractorStatus.OK) {
			return CegarStatus.OK;
		} else if (refiner.getStatus() == CexStatus.CONCRETE) {
			return CegarStatus.CEX;
		} else {
			throw new IllegalStateException();
		}
	}

	public Trace<CS, A> getCex() {
		checkState(refiner.getStatus() == CexStatus.CONCRETE);
		return refiner.getConcreteCex();
	}
}
