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

	private final Abstractor<S, A, P> abstractor;
	private final Refiner<S, A, P> refiner;

	private CegarChecker(final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
	}

	public static <S extends State, A extends Action, P extends Precision> CegarChecker<S, A, P> create(
			final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner) {
		return new CegarChecker<>(abstractor, refiner);
	}

	@Override
	public SafetyStatus<S, A> check(final P initPrecision) {
		RefinerResult<S, A, P> refinerStatus = null;
		AbstractorResult abstractorStatus = null;
		final ARG<S, A> arg = abstractor.createArg();
		P precision = initPrecision;
		do {
			abstractorStatus = abstractor.check(arg, precision);

			if (abstractorStatus.isUnsafe()) {
				refinerStatus = refiner.refine(arg, precision);

				if (refinerStatus.isSpurious()) {
					precision = refinerStatus.asSpurious().getRefinedPrecision();
				}
			}

		} while (!abstractorStatus.isSafe() && !refinerStatus.isUnsafe());

		assert abstractorStatus != null;
		assert abstractorStatus.isSafe() || refinerStatus != null;

		if (abstractorStatus.isSafe()) {
			return SafetyStatus.safe(arg);
		} else if (refinerStatus.isUnsafe()) {
			return SafetyStatus.unsafe(refinerStatus.asUnsafe().getCex(), arg);
		} else {
			throw new IllegalStateException();
		}
	}
}
