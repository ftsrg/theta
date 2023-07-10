/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.bmc;

import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Tuple5;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.PathUtils;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.solver.Solver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory.indexing;

public class IterativeBmcChecker<S extends ExprState, A extends StmtAction, P extends Prec> implements
        SafetyChecker<S, A, P> {

    private final LTS<S, A> lts;
    private final InitFunc<S, P> initFunc;
    private final TransFunc<S, A, P> transFunc;
    private final Predicate<S> unsafePredicate;
    private final Solver solver;
    private final int upperBound;
    private final int stepSize;
    private final Logger logger;

    private IterativeBmcChecker(final LTS<S, A> lts,
                                final InitFunc<S, P> initFunc,
                                final TransFunc<S, A, P> transFunc,
                                final Predicate<S> unsafePredicate,
                                final Solver solver,
                                final Logger logger,
                                final int upperBound,
                                final int stepSize) {
        this.lts = lts;
        this.initFunc = initFunc;
        this.transFunc = transFunc;
        this.unsafePredicate = unsafePredicate;
        this.solver = solver;
        this.logger = logger;
        this.upperBound = upperBound;
        this.stepSize = stepSize;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> IterativeBmcChecker<S, A, P> create(
            final LTS<S, A> lts,
            final InitFunc<S, P> initFunc,
            final TransFunc<S, A, P> transFunc,
            final Predicate<S> unsafePredicate,
            final Solver solver,
            final Logger logger,
            final int upperBound,
            final int stepSize) {
        return new IterativeBmcChecker<S, A, P>(lts, initFunc, transFunc, unsafePredicate, solver,
                logger, upperBound, stepSize);
    }

    private final Collection<Tuple5<Trace<S, A>, VarIndexing, S, A, Collection<Expr<BoolType>>>> resumeSet = new LinkedHashSet<>();

    @Override
    public SafetyResult<S, A> check(P prec) {
        logger.write(Logger.Level.INFO, "Configuration: %s%n", this);

        boolean isSafe = true;
        for (S initState : initFunc.getInitStates(prec)) {
            logger.write(Logger.Level.INFO, "Checking from state %s with a bound of %d%n",
                    initState, stepSize);
            final SafetyResult<S, A> result = check(null, indexing(0), initState, null, prec,
                    stepSize, 0);
            if (result == null) {
                isSafe = false;
            } else if (result.isUnsafe()) {
                logger.write(Logger.Level.RESULT, "%s%n", result);
                return result;
            }
        }
        if (isSafe) {
            final SafetyResult.Safe<S, A> result = SafetyResult.safe(ARG.create(
                    (state1, state2) -> false));// TODO: this is only a placeholder, we don't give back an ARG)
            logger.write(Logger.Level.RESULT, "%s%n", result);
            return result;
        }

        // From here on, proving safety is only possible if all paths are enumareted
        for (int bound = stepSize; (upperBound < 0 || bound <= upperBound) && resumeSet.size() > 0;
             bound += stepSize) {
            final Collection<Tuple5<Trace<S, A>, VarIndexing, S, A, Collection<Expr<BoolType>>>> localResumeSet = new LinkedHashSet<>(
                    resumeSet);
            resumeSet.clear();
            for (Tuple5<Trace<S, A>, VarIndexing, S, A, Collection<Expr<BoolType>>> resumePoint : localResumeSet) {
                logger.write(Logger.Level.INFO,
                        "Resuming from state %s with a bound of %d (current depth: %d)%n",
                        resumePoint.get1().getState(resumePoint.get1().getStates().size() - 1),
                        stepSize + bound, bound);
                solver.push();
                solver.add(resumePoint.get5());
                final SafetyResult<S, A> result = check(resumePoint.get1(), resumePoint.get2(),
                        resumePoint.get3(), resumePoint.get4(), prec, bound + stepSize, bound);
                solver.pop();
                if (result != null && result.isUnsafe()) {
                    logger.write(Logger.Level.RESULT, "%s%n", result);
                    return result;
                }
            }
        }

        if (resumeSet.size() == 0) {
            final SafetyResult.Safe<S, A> result = SafetyResult.safe(ARG.create(
                    (state1, state2) -> false));// TODO: this is only a placeholder, we don't give back an ARG)
            logger.write(Logger.Level.RESULT, "%s%n", result);
            return result;
        }

        SafetyResult<S, A> bmcresult = SafetyResult.safe(ARG.create(
                (state1, state2) -> false)); // TODO: this is only a placeholder, we don't give back an ARG
        logger.write(Logger.Level.RESULT, "BmcOutOfBounds: %s%n", bmcresult);
        return bmcresult;
    }


    private SafetyResult<S, A> check(final Trace<S, A> trace, final VarIndexing varIndexing,
                                     final S state, final A action, final P prec, final int bound, final int currentStep) {
        final Trace<S, A> nextTrace;
        if (trace == null) {
            nextTrace = Trace.of(List.of(state), List.<A>of());
        } else {
            nextTrace = Trace.of(
                    Streams.concat(trace.getStates().stream(), Stream.of(state))
                            .collect(Collectors.toList()),
                    Streams.concat(trace.getActions().stream(), Stream.of(action))
                            .collect(Collectors.toList()));
        }
        if (unsafePredicate.test(state)) {
            return SafetyResult.unsafe(trace, ARG.create(
                    (state1, state2) -> false)); // TODO: this is only a placeholder, we don't give back an ARG
        }

        if (currentStep >= bound) {
            final Collection<Expr<BoolType>> assertions = new ArrayList<>(solver.getAssertions());
            resumeSet.add(Tuple5.of(trace, varIndexing, state, action, assertions));
            return null;
        }

        boolean isSafe = true;
        for (final A a : lts.getEnabledActionsFor(state)) {
            solver.push();
            solver.add(PathUtils.unfold(a.toExpr(), varIndexing));
            if (solver.check().isSat()) {
                for (final S succState : transFunc.getSuccStates(state, a, prec)) {
                    if (!succState.isBottom()) {
                        final SafetyResult<S, A> result = check(nextTrace,
                                varIndexing.add(a.nextIndexing()), succState, a, prec, bound,
                                currentStep + 1);
                        if (result != null && result.isUnsafe()) {
                            solver.pop();
                            return result;
                        } else if (result == null) {
                            isSafe = false;
                        }
                    }
                }
            }
            solver.pop();
        }
        if (isSafe) {
            return SafetyResult.safe(ARG.create(
                    (state1, state2) -> false)); // TODO: this is only a placeholder, we don't give back an ARG)
        }
        return null;
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).add(upperBound).add(lts)
                .add(initFunc).add(transFunc).add(unsafePredicate).toString();
    }
}
