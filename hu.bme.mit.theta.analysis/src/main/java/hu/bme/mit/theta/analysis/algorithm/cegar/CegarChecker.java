package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Precision;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyStatus;
import hu.bme.mit.theta.analysis.algorithm.Statistics;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;

public final class CegarChecker<S extends State, A extends Action, P extends Precision>
		implements SafetyChecker<S, A, P> {

	private final Abstractor<S, A, P> abstractor;
	private final Refiner<S, A, P> refiner;
	private final Logger logger;

	private CegarChecker(final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner, final Logger logger) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
		this.logger = checkNotNull(logger);
	}

	public static <S extends State, A extends Action, P extends Precision> CegarChecker<S, A, P> create(
			final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner) {
		return new CegarChecker<>(abstractor, refiner, NullLogger.getInstance());
	}

	public static <S extends State, A extends Action, P extends Precision> CegarChecker<S, A, P> create(
			final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner, final Logger logger) {
		return new CegarChecker<>(abstractor, refiner, logger);
	}

	@Override
	public SafetyStatus<S, A> check(final P initPrecision) {
		final Stopwatch stopwatch = Stopwatch.createStarted();
		RefinerResult<S, A, P> refinerResult = null;
		AbstractorResult abstractorResult = null;
		final ARG<S, A> arg = abstractor.createArg();
		P precision = initPrecision;
		int iteration = 0;
		do {
			++iteration;

			logger.writeln("Iteration " + iteration, 2);
			logger.writeln("Checking abstraction...", 2, 1);
			logger.write("Precision: ", 3, 2).writeln(precision, 3);

			abstractorResult = abstractor.check(arg, precision);

			logger.write("Checking abstraction done, result: ", 2, 1).writeln(abstractorResult, 2);

			if (abstractorResult.isUnsafe()) {
				logger.writeln("Refining abstraction...", 2, 1);
				refinerResult = refiner.refine(arg, precision);
				logger.write("Refining abstraction done, result: ", 2, 1).writeln(refinerResult, 2);

				if (refinerResult.isSpurious()) {
					precision = refinerResult.asSpurious().getRefinedPrecision();
				}
			}

		} while (!abstractorResult.isSafe() && !refinerResult.isUnsafe());

		assert abstractorResult.isSafe() || refinerResult != null;

		stopwatch.stop();
		SafetyStatus<S, A> cegarResult = null;
		final Statistics stats = new Statistics(stopwatch.elapsed(TimeUnit.MILLISECONDS), iteration);

		if (abstractorResult.isSafe()) {
			cegarResult = SafetyStatus.safe(arg, stats);
		} else if (refinerResult.isUnsafe()) {
			cegarResult = SafetyStatus.unsafe(refinerResult.asUnsafe().getCex(), arg, stats);
		} else {
			throw new IllegalStateException();
		}

		assert cegarResult != null;
		logger.write("Done, result: ", 1).writeln(cegarResult, 1);
		logger.writeln(stats, 1);
		return cegarResult;
	}
}
