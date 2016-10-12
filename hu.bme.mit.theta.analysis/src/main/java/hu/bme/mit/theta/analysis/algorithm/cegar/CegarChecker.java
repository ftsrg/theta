package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;

public class CegarChecker<S extends State, A extends Action, P extends Precision, CS extends State>
		implements SafetyChecker<S, A, P> {

	private final Abstractor<S, A, ? super P> abstractor;
	private final Refiner<S, A, P, CS> refiner;

	public CegarChecker(final Abstractor<S, A, ? super P> abstractor, final Refiner<S, A, P, CS> refiner) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
	}

	@Override
	public SafetyStatus<S, A> check(final P initPrecision) {

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

		} while (abstractor.getStatus() != AbstractorStatus.OK && refiner.getStatus() != CexStatus.CONCRETE);

		return extractStatus();
	}

	public SafetyStatus<S, A> extractStatus() {
		if (abstractor.getStatus() == AbstractorStatus.OK) {
			return SafetyStatus.safe(abstractor.getARG());
		} else if (refiner.getStatus() == CexStatus.CONCRETE) {
			return SafetyStatus.unsafe(refiner.getCex());
		} else {
			throw new IllegalStateException();
		}
	}

}
