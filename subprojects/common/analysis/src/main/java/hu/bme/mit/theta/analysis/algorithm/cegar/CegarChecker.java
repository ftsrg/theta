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

import com.google.common.base.Stopwatch;
import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.ArgNode;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.common.visualization.Graph;
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;

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

	// controlled restart
	//private Set<AbstractArg> args = new LinkedHashSet<>();
	private static NotSolvableThrower notSolvableThrower = null;

	// counterexample checks
	private CexStorage<S, A> cexStorage = new CexStorage<S, A>();
	private boolean noNewCex = false;
	private boolean argNotNew = false;

	public static void setNotSolvableThrower(NotSolvableThrower thrower) {
		notSolvableThrower = thrower;
	}

	private CegarChecker(final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner, final Logger logger) {
		this.abstractor = checkNotNull(abstractor);
		abstractor.addCexStorage(cexStorage);
		this.refiner = checkNotNull(refiner);
		refiner.addCexStorage(cexStorage);
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

	/*
	private class AbstractArg {
		private final Collection<State> states;
		// private final P prec;

		private AbstractArg(final Stream<ArgNode<S, A>> nodes) { //, final P prec){
			states = nodes.map(ArgNode::getState).collect(Collectors.toList());
			// this.prec = prec;
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			AbstractArg that = (AbstractArg) o;
			return (states.equals(that.states)); //&& prec.equals(that.prec));
		}

		@Override
		public int hashCode() {
			return Objects.hash(states);
		}

		//public int hashCode() {
		//	return Objects.hash(states, prec);
		//}

	}
	*/

	@Override
	public SafetyResult<S, A> check(final P initPrec) {
		logger.write(Level.INFO, "Configuration: %s%n", this);
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

			logger.write(Level.MAINSTEP, "Iteration %d%n", iteration);
			logger.write(Level.MAINSTEP, "| Checking abstraction...%n");
			final long abstractorStartTime = stopwatch.elapsed(TimeUnit.MILLISECONDS);
			abstractorResult = abstractor.check(arg, prec);
			abstractorTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - abstractorStartTime;
			logger.write(Level.MAINSTEP, "| Checking abstraction done, result: %s%n", abstractorResult);

			logger.write(Level.VERBOSE, "Printing ARG..." + System.lineSeparator());
			Graph g = ArgVisualizer.getDefault().visualize(arg);
			logger.write(Level.VERBOSE, GraphvizWriter.getInstance().writeString(g) + System.lineSeparator());
			/*
			if(args.contains(new AbstractArg(arg.getNodes()))) {
				logger.write(Level.MAINSTEP, "! ARG is NOT NEW"+System.lineSeparator());
				argNotNew = true;
			} else {
				logger.write(Level.MAINSTEP, "! ARG is NEW"+System.lineSeparator());
				argNotNew = false;
			}
			args.add(new AbstractArg(arg.getNodes()));
			 */

			if (abstractorResult.isUnsafe()) {
				// stopping verification, if there is no new cex to refine AND the precision did not change (it would stop with an error in the refiner anyways)
				//if(notSolvableThrower!= null && arg.getCexs().noneMatch(cex -> cexStorage.checkIfCounterexampleNew(cex))) {
					// notSolvableThrower.throwNoNewCexException();
					// noNewCex = true;
				// } else {
					// noNewCex = false;
				// }

				P lastPrec = prec;
				logger.write(Level.MAINSTEP, "| Refining abstraction...%n");
				final long refinerStartTime = stopwatch.elapsed(TimeUnit.MILLISECONDS);
				refinerResult = refiner.refine(arg, prec);
				refinerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - refinerStartTime;
				logger.write(Level.MAINSTEP, "Refining abstraction done, result: %s%n", refinerResult);

				if (refinerResult.isSpurious()) {
					prec = refinerResult.asSpurious().getRefinedPrec();
				}

				if(lastPrec.equals(prec)) {
					logger.write(Level.MAINSTEP, "! Precision did NOT change in this iteration"+System.lineSeparator());
					// if(noNewCex && argNotNew) { // the precision did not change, there was no new cex added before that AND the cex was spurious -> stuck
					//	notSolvableThrower.throwNoNewCexException();
					//}
				} else {
					logger.write(Level.MAINSTEP, "! Precision DID change in this iteration"+System.lineSeparator());
				}
			}

			cexStorage.endOfIteration();

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
		logger.write(Level.RESULT, "%s%n", cegarResult);
		logger.write(Level.INFO, "%s%n", stats);
		return cegarResult;
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(getClass().getSimpleName()).add(abstractor).add(refiner).toString();
	}
}
