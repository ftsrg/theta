/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.runtimemonitor.MonitorCheckpoint;
import hu.bme.mit.theta.analysis.utils.ArgVisualizer;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.common.logging.NullLogger;

import hu.bme.mit.theta.common.visualization.writer.JSONWriter;
import hu.bme.mit.theta.common.visualization.writer.WebDebuggerLogger;

import java.util.concurrent.TimeUnit;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Counterexample-Guided Abstraction Refinement (CEGAR) loop implementation,
 * that uses an Abstractor to explore the abstract state space and a Refiner to
 * check counterexamples and refine them if needed. It also provides certain
 * statistics about its execution.
 */
public final class CegarChecker<S extends State, A extends Action, P extends Prec> implements SafetyChecker<ARG<S, A>, Trace<S, A>, P> {

    private final Abstractor<S, A, P> abstractor;
    private final Refiner<S, A, P> refiner;
    private final Logger logger;
    private final ARG<S, A> arg; // TODO I don't think putting the ARG up here from check below causes any issues, but keep it in mind, that it might

    private CegarChecker(final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner, final Logger logger) {
        this.abstractor = checkNotNull(abstractor);
        this.refiner = checkNotNull(refiner);
        this.logger = checkNotNull(logger);
        arg = abstractor.createArg();
    }

    public static <S extends State, A extends Action, P extends Prec> CegarChecker<S, A, P> create(
            final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner) {
        return new CegarChecker<>(abstractor, refiner, NullLogger.getInstance());
    }

    public static <S extends State, A extends Action, P extends Prec> CegarChecker<S, A, P> create(
            final Abstractor<S, A, P> abstractor, final Refiner<S, A, P> refiner, final Logger logger) {
        return new CegarChecker<>(abstractor, refiner, logger);
    }

    public ARG<S, A> getArg() {
        return arg;
    }

    @Override
    public SafetyResult<ARG<S, A>, Trace<S, A>> check(final P initPrec) {
        logger.write(Level.INFO, "Configuration: %s%n", this);
        final Stopwatch stopwatch = Stopwatch.createStarted();
        long abstractorTime = 0;
        long refinerTime = 0;
        RefinerResult<S, A, P> refinerResult = null;
        AbstractorResult abstractorResult = null;
        P prec = initPrec;
        int iteration = 0;
        WebDebuggerLogger wdl = WebDebuggerLogger.getInstance();
        do {
            ++iteration;

            logger.write(Level.MAINSTEP, "Iteration %d%n", iteration);
            logger.write(Level.MAINSTEP, "| Checking abstraction...%n");
            final long abstractorStartTime = stopwatch.elapsed(TimeUnit.MILLISECONDS);
            abstractorResult = abstractor.check(arg, prec);
            abstractorTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - abstractorStartTime;
            logger.write(Level.MAINSTEP, "| Checking abstraction done, result: %s%n", abstractorResult);

            if (WebDebuggerLogger.enabled()) {
                String argGraph = JSONWriter.getInstance().writeString(ArgVisualizer.getDefault().visualize(arg));
                String precString = prec.toString();
                wdl.addIteration(iteration, argGraph, precString);
            }

            if (abstractorResult.isUnsafe()) {
                MonitorCheckpoint.Checkpoints.execute("CegarChecker.unsafeARG");

                P lastPrec = prec;
                logger.write(Level.MAINSTEP, "| Refining abstraction...%n");
                final long refinerStartTime = stopwatch.elapsed(TimeUnit.MILLISECONDS);
                refinerResult = refiner.refine(arg, prec);
                refinerTime += stopwatch.elapsed(TimeUnit.MILLISECONDS) - refinerStartTime;
                logger.write(Level.MAINSTEP, "Refining abstraction done, result: %s%n", refinerResult);

                if (refinerResult.isSpurious()) {
                    prec = refinerResult.asSpurious().getRefinedPrec();
                }

                if (lastPrec.equals(prec)) {
                    logger.write(Level.MAINSTEP, "! Precision did NOT change in this iteration" + System.lineSeparator());
                } else {
                    logger.write(Level.MAINSTEP, "! Precision DID change in this iteration" + System.lineSeparator());
                }

            }

        } while (!abstractorResult.isSafe() && !refinerResult.isUnsafe());

        stopwatch.stop();
        SafetyResult<ARG<S, A>, Trace<S, A>> cegarResult = null;
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
