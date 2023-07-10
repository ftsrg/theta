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

import com.google.common.collect.Lists;
import hu.bme.mit.theta.analysis.InitFunc;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.TransFunc;
import hu.bme.mit.theta.analysis.algorithm.ARG;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.analysis.expr.StmtAction;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.Solver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class BmcChecker<S extends ExprState, A extends StmtAction, P extends Prec> implements
        SafetyChecker<S, A, P> {

    private final LTS<S, A> lts;
    private final InitFunc<S, P> initFunc;
    private final TransFunc<S, A, P> transFunc;
    private final Predicate<S> unsafePredicate;
    private final Solver solver;
    private final int upperBound;
    private final Logger logger;
    private final boolean onlyFeasible; // only keep feasible traces (i.e. test in each iteration)

    private BmcChecker(final LTS<S, A> lts,
                       final InitFunc<S, P> initFunc,
                       final TransFunc<S, A, P> transFunc,
                       final Predicate<S> unsafePredicate,
                       final Solver solver,
                       final Logger logger,
                       final int upperBound, boolean onlyFeasible) {
        this.lts = lts;
        this.initFunc = initFunc;
        this.transFunc = transFunc;
        this.unsafePredicate = unsafePredicate;
        this.solver = solver;
        this.upperBound = upperBound;
        this.logger = logger;
        this.onlyFeasible = onlyFeasible;
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> BmcChecker<S, A, P> create(
            final LTS<S, A> lts,
            final InitFunc<S, P> initFunc,
            final TransFunc<S, A, P> transFunc,
            final Predicate<S> unsafePredicate,
            final Solver solver,
            final Logger logger,
            final int upperBound,
            final boolean onlyFeasible) {
        return new BmcChecker<S, A, P>(lts, initFunc, transFunc, unsafePredicate, solver, logger,
                upperBound, onlyFeasible);
    }

    public static <S extends ExprState, A extends StmtAction, P extends Prec> BmcChecker<S, A, P> create(
            final LTS<S, A> lts,
            final InitFunc<S, P> initFunc,
            final TransFunc<S, A, P> transFunc,
            final Predicate<S> unsafePredicate,
            final Solver solver,
            final Logger logger,
            final boolean onlyFeasible) {
        return new BmcChecker<S, A, P>(lts, initFunc, transFunc, unsafePredicate, solver, logger,
                -1, onlyFeasible);
    }

    @Override
    public SafetyResult<S, A> check(P prec) {
        logger.write(Logger.Level.INFO, "Configuration: %s%n", this);
        final Collection<? extends S> initStates = initFunc.getInitStates(prec);
        final List<BmcTrace<S, A>> traces = initStates.stream()
                .map(s -> BmcTrace.of(List.<S>of(s), List.<A>of()))
                .collect(Collectors.toCollection(LinkedList::new));
        int currentBound = 0;
        SafetyResult<S, A> bmcresult = null;
        outerloop:
        while ((upperBound < 0 || currentBound < upperBound) && traces.size() > 0) {
            currentBound++;
            logger.write(Logger.Level.MAINSTEP, "Iteration %d%n", currentBound);
            logger.write(Logger.Level.MAINSTEP, "| Current traces: %d%n", traces.size());
            logger.write(Logger.Level.MAINSTEP, "| Expanding traces...%n");
            int size = traces.size();
            final List<Integer> toRemove = new ArrayList<>();
            for (int i = 0; i < size; i++) {
                BmcTrace<S, A> t = traces.get(i);
                checkState(t.length() == currentBound - 1, "Trace " + t + " not well formatted");
                final S lastState = t.getLastState();
                final Collection<A> actions = lts.getEnabledActionsFor(lastState);
                int actionCnt = 0;
                int addCount = 0;
                for (A a : actions) {
                    actionCnt++;
                    final Collection<? extends S> states = transFunc.getSuccStates(lastState, a,
                            prec);
                    int stateCnt = 0;
                    for (S succState : states) {
                        stateCnt++;
                        final BmcTrace<S, A> trace;
                        final int idx;
                        addCount++;
                        if (actions.size() == actionCnt && states.size() == stateCnt) {
                            trace = t.addState(succState, a);
                            idx = i;
                        } else {
                            trace = t.copy().addState(succState, a);
                            idx = traces.size();
                            traces.add(trace);
                        }
                        if (onlyFeasible) {
                            final boolean feasible = trace.isFeasible(solver);
                            if (feasible) {
                                final boolean unsafe = unsafePredicate.test(succState);
                                if (unsafe) {
                                    bmcresult = SafetyResult.unsafe(trace.toImmutableTrace(),
                                            ARG.create(
                                                    (state1, state2) -> false)); // TODO: this is only a placeholder, we don't give back an ARG
                                    break outerloop;
                                }
                            } else {
                                addCount--;
                                traces.remove(idx);
                                if (idx <= i) {
                                    size--;
                                    i--;
                                }
                            }
                        } else {
                            if (unsafePredicate.test(succState) && trace.isFeasible(solver)) {
                                bmcresult = SafetyResult.unsafe(trace.toImmutableTrace(),
                                        ARG.create(
                                                (state1, state2) -> false)); // TODO: this is only a placeholder, we don't give back an ARG
                                break outerloop;
                            }
                        }
                    }
                }
                if (addCount == 0) {
                    traces.remove(i);
                    size--;
                    i--;
                }
            }
            for (int idx : Lists.reverse(toRemove)) {
                traces.remove(idx);
            }
        }
        if (bmcresult == null) {
            bmcresult = SafetyResult.safe(ARG.create(
                    (state1, state2) -> false)); // TODO: this is only a placeholder, we don't give back an ARG
        }
        logger.write(Logger.Level.RESULT, "%s%n", bmcresult);
        return bmcresult;
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).add(upperBound).add(lts)
                .add(initFunc).toString();
    }
}
