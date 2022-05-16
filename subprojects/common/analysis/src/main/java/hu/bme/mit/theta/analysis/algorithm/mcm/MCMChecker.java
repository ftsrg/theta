/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.PartialOrd;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.mcm.cegar.AbstractExecutionGraph;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.analysis.algorithm.mcm.MemoryEvent.MemoryEventType.READ;
import static hu.bme.mit.theta.analysis.algorithm.mcm.MemoryEvent.MemoryEventType.WRITE;

public class MCMChecker<S extends State, A extends Action, P extends Prec> {
    private final MemoryEventProvider<S, A> memoryEventProvider;
    private final MultiprocLTS<S, A> multiprocLTS;
    private final MultiprocInitFunc<S, P> multiprocInitFunc;
    private final MultiprocTransFunc<S, A, P> multiprocTransFunc;
    private final Collection<Integer> pids;
    private final Collection<MemoryEvent.Write> initialWrites;
    private final PartialOrd<S> partialOrd;
    private final Solver solver;
    private final MCM mcm;
    private final Logger logger;

    public MCMChecker(
            final MemoryEventProvider<S, A> memoryEventProvider,
            final MultiprocLTS<S, A> multiprocLTS,
            final MultiprocInitFunc<S, P> multiprocInitFunc,
            final MultiprocTransFunc<S, A, P> multiprocTransFunc,
            final Collection<Integer> pids,
            final Collection<MemoryEvent.Write> initialWrites,
            final PartialOrd<S> partialOrd,
            final Solver solver,
            final MCM mcm,
            final Logger logger) {
        this.initialWrites = initialWrites;
        this.partialOrd = partialOrd;
        checkArgument(pids.stream().noneMatch(i -> i >= 0), "Meta event IDs must be negative!");

        this.memoryEventProvider = memoryEventProvider;
        this.multiprocLTS = multiprocLTS;
        this.multiprocInitFunc = multiprocInitFunc;
        this.multiprocTransFunc = multiprocTransFunc;
        this.pids = pids;
        this.solver = solver;
        this.mcm = mcm;
        this.logger = logger;
    }

    public MCMSafetyResult check(final P prec) {
        logger.write(Logger.Level.MAINSTEP, "Starting verification\n");
        final AbstractExecutionGraph<S, A> executionGraph = new AbstractExecutionGraph<S, A>(List.of("RX", "A", "DMB.SY", "thread-end"), solver, this.mcm, partialOrd);

        final List<Integer> initialWriteEvents = new ArrayList<>();

        for (MemoryEvent.Write initialWrite : initialWrites) {
            int i = executionGraph.addInitialWrite(initialWrite.varId(), Set.of());
            initialWriteEvents.add(i);
        }
        logger.write(Logger.Level.SUBSTEP, "|-- Added initial writes: " + initialWriteEvents.size() + "\n");

        final List<List<Integer>> events = new ArrayList<>();

        for (final int pid : pids) {
            logger.write(Logger.Level.SUBSTEP, "|-- Starting exploration of pid " + pid + "\n");
            final Map<MemoryEvent.Read, Integer> reads = new LinkedHashMap<>();
            final List<Integer> eventList = new ArrayList<>();
            events.add(eventList);

            final Collection<? extends S> initStates = multiprocInitFunc.getInitStates(pid, prec);
            checkState(initStates.size() == 1);

            int lastId = 0;
            S state = null;
            for (final S initState : initStates) { // will only execute once
                state = initState;
            }

            final Collection<Tuple2<Integer, S>> descriptorSet = new LinkedHashSet<>();
            descriptorSet.add(Tuple2.of(lastId, state));

            while(true) {
                Optional<Tuple2<Integer, S>> any = descriptorSet.stream().findAny();
                if(!any.isPresent()) break;
                descriptorSet.remove(any.get());
                lastId = any.get().get1();
                state = any.get().get2();

                final Collection<A> enabledActionsFor = multiprocLTS.getEnabledActionsFor(pid, state);
                if (enabledActionsFor.size() == 0) break;
                for (final A a : enabledActionsFor) {
                    int savedLastId = lastId;
                    S savedState = state;
                    final Collection<MemoryEvent> memoryEventsOf = memoryEventProvider.getMemoryEventsOf(savedState, a);
                    for (MemoryEvent memoryEvent : memoryEventsOf) {
                        savedLastId = executionGraph.addMemoryEvent(memoryEvent, pid, savedLastId);
                        logger.write(Logger.Level.SUBSTEP, "|------ Adding memory event #" + savedLastId + ": " + memoryEvent + "\n");

                        if (memoryEvent.type() == READ) reads.put(memoryEvent.asRead(), savedLastId);
                        else if (memoryEvent.type() == WRITE) {
                            for (MemoryEvent.Read read : reads.keySet()) {
                                if (memoryEvent.asWrite().dependencies().contains(read.localVar())) {
                                    executionGraph.addDataDependency(reads.get(read), savedLastId);
                                }
                            }
                        }

                        eventList.add(savedLastId);
                    }
                    final Collection<? extends S> succStates = multiprocTransFunc.getSuccStates(pid, savedState, a, prec);
                    checkState(succStates.size() == 1);
                    for (final S succState : succStates) { // will execute only once
                        savedState = succState;
                    }
                    descriptorSet.add(Tuple2.of(savedLastId, savedState));
                }
            }
        }

        final Collection<Map<Decl<?>, LitExpr<?>>> solutions = new ArrayList<>();
        EventConstantLookup rf = executionGraph.encode();

        logger.write(Logger.Level.SUBSTEP, "|-- Successfully built execution graph\n");
        while(executionGraph.nextSolution(solutions)) {
            logger.write(Logger.Level.SUBSTEP, "|-- Found new solution: " + executionGraph.getRf() + "\n");
        }

        logger.write(Logger.Level.RESULT, "Number of executions: " + solutions.size() + "\n");
        logger.write(Logger.Level.MAINSTEP, "Verification ended\n");
        return new MCMSafetyResult(solutions, events, initialWriteEvents);
    }

    public static class MCMSafetyResult {
        private final Collection<Map<Decl<?>, LitExpr<?>>> solutions;
        private final List<List<Integer>> events;
        private final List<Integer> initialWriteEvents;

        public MCMSafetyResult(Collection<Map<Decl<?>, LitExpr<?>>> solutions, List<List<Integer>> events, List<Integer> initialWriteEvents) {
            this.solutions = solutions;
            this.events = events;
            this.initialWriteEvents = initialWriteEvents;
        }

        public Collection<Map<Decl<?>, LitExpr<?>>> getSolutions() {
            return solutions;
        }

        public List<List<Integer>> getEvents() {
            return events;
        }

        public List<Integer> getInitialWriteEvents() {
            return initialWriteEvents;
        }

        public void visualize() {
            new Thread(new ExecutionGraphVisualizer(solutions, events, initialWriteEvents)).start();
        }
    }
}
