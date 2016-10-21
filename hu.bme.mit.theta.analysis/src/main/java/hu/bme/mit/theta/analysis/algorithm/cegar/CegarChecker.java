package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;

public final class CegarChecker<S extends State, A extends Action, P extends Precision>
		implements SafetyChecker<S, A, P> {

	private final Abstractor<S, A, ? super P> abstractor;
	private final Refiner<S, A, P> refiner;

	private CegarChecker(final Abstractor<S, A, ? super P> abstractor, final Refiner<S, A, P> refiner) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
	}

	public static <S extends State, A extends Action, P extends Precision> CegarChecker<S, A, P> create(
			final Abstractor<S, A, ? super P> abstractor, final Refiner<S, A, P> refiner) {
		return new CegarChecker<>(abstractor, refiner);
	}

	@Override
	public SafetyStatus<S, A> check(final P initPrecision) {

		P precision = initPrecision;
		do {

			abstractor.init(precision); // TODO: currently the ARG is not
										// pruned, so the abstractor simply
										// restarts at every iteration
			abstractor.check(precision);

			if (abstractor.getStatus().isUnsafe()) {
				final ARG<S, A> arg = abstractor.getARG();
				refiner.refine(arg, precision);

				if (refiner.getStatus().isSpurious()) {
					precision = refiner.getStatus().asSpurious().getRefinedPrecision();
				}
			}

		} while (!abstractor.getStatus().isSafe() && !refiner.getStatus().isConcretizable());

		return extractStatus();
	}

	public SafetyStatus<S, A> extractStatus() {
		if (abstractor.getStatus().isSafe()) {
			return SafetyStatus.safe(abstractor.getARG());
		} else if (refiner.getStatus().isConcretizable()) {
			return SafetyStatus.unsafe(refiner.getStatus().asConcretizable().getCex());
		} else {
			throw new IllegalStateException();
		}
	}

}
