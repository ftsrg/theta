/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.analysis.algorithm.cegar;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.concurrent.TimeUnit;

import com.google.common.base.Stopwatch;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.impl.NullLogger;

/**
 * Counterexample-Guided Abstraction Refinement (CEGAR) loop implementation,
 * that uses an Abstractor to explore the abstract state space and a Refiner to
 * check counterexamples and refine them if needed. It also provides certain
 * statistics about its execution.
 */
public final class CegarChecker<S extends State, A extends Action, P extends Prec> implements SafetyChecker<S, A, P> {

	private final Abstractor<S, A, P> abstractor;
	private final Refiner<S, A, P> refiner;
	private final Logger logger;

	private CegarChecker(final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner, final Logger logger) {
		this.abstractor = checkNotNull(abstractor);
		this.refiner = checkNotNull(refiner);
		this.logger = checkNotNull(logger);
	}

	public static <S extends State, A extends Action, P extends Prec> CegarChecker<S, A, P> create(
			final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner) {
		return new CegarChecker<>(abstractor, refiner, NullLogger.getInstance());
	}

	public static <S extends State, A extends Action, P extends Prec> CegarChecker<S, A, P> create(
			final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner, final Logger logger) {
		return new CegarChecker<>(abstractor, refiner, logger);
	}

	@Override
	public SafetyResult<S, A> check(final P initPrec) {
		logger.writeln("Configuration: ", this, 1, 0);
		final Stopwatch stopwatch = Stopwatch.createStarted();
		long abstractorTime = 0;
		long refinerTime = 0;
		RefinerResult<S, A, P> refinerResult = null;
		AbstractorResult abstractorResult = null;
		final ARG<S, A> arg = abstractor.createArg();
		P prec = initPrec;
		int iteration = 0;
		do {
			++iteration;
			logger.writeln("Iteration ", iteration, 2, 0);

			logger.writeln("Checking abstraction...", 2, 1);
			final long abstractorStartTime = stopwatch.elapsed(TimeUnit.MILLISECONDS);
			abstractorResult = abstractor.check(arg, prec);
			abstractorTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - abstractorStartTime;
			logger.writeln("Checking abstraction done, result: ", abstractorResult, 2, 1);

			if (abstractorResult.isUnsafe()) {
				logger.writeln("Refining abstraction...", 2, 1);
				final long refinerStartTime = stopwatch.elapsed(TimeUnit.MILLISECONDS);
				refinerResult = refiner.refine(arg, prec);
				refinerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - refinerStartTime;
				logger.writeln("Refining abstraction done, result: ", refinerResult, 2, 1);

				if (refinerResult.isSpurious()) {
					prec = refinerResult.asSpurious().getRefinedPrec();
				}
			}

		} while (!abstractorResult.isSafe() && !refinerResult.isUnsafe());

		stopwatch.stop();
		SafetyResult<S, A> cegarResult = null;
		final CegarStatistics stats = new CegarStatistics(stopwatch.elapsed(TimeUnit.MILLISECONDS), abstractorTime,
				refinerTime, iteration);

		assert abstractorResult.isSafe() || (refinerResult != null && refinerResult.isUnsafe());

		if (abstractorResult.isSafe()) {
			cegarResult = SafetyResult.safe(arg, stats);
		} else if (refinerResult.isUnsafe()) {
			cegarResult = SafetyResult.unsafe(refinerResult.asUnsafe().getCex(), arg, stats);
		}

		assert cegarResult != null;
		logger.writeln("Done, result: ", cegarResult, 1, 0);
		logger.writeln(stats, 1);
		return cegarResult;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).add(abstractor).add(refiner).toString();
	}
}
