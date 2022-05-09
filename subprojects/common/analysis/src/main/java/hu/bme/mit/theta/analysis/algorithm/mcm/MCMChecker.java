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
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.analysis.algorithm.mcm.MemoryEvent.MemoryEventType.READ;
import static hu.bme.mit.theta.analysis.algorithm.mcm.MemoryEvent.MemoryEventType.WRITE;

public class MCMChecker<S extends State, A extends Action, P extends Prec> implements SafetyChecker<S, A, P> {
    private final MemoryEventProvider<S, A> memoryEventProvider;
    private final MultiprocLTS<S, A> multiprocLTS;
    private final MultiprocInitFunc<S, P> multiprocInitFunc;
    private final MultiprocTransFunc<S, A, P> multiprocTransFunc;
    private final Collection<Integer> pids;
    private final Collection<MemoryEvent> initialWrites;
    private final Collection<String> tags;
    private final Solver solver;
    private final MCM mcm;

    public MCMChecker(
            final MemoryEventProvider<S, A> memoryEventProvider,
            final MultiprocLTS<S, A> multiprocLTS,
            final MultiprocInitFunc<S, P> multiprocInitFunc,
            final MultiprocTransFunc<S, A, P> multiprocTransFunc,
            final Collection<Integer> pids,
            final Collection<MemoryEvent> initialWrites,
            final Collection<String> tags,
            final Solver solver,
            final MCM mcm) {
        this.initialWrites = initialWrites;
        this.tags = tags;
        checkArgument(pids.stream().noneMatch(i -> i >= 0), "Meta event IDs must be negative!");

        this.memoryEventProvider = memoryEventProvider;
        this.multiprocLTS = multiprocLTS;
        this.multiprocInitFunc = multiprocInitFunc;
        this.multiprocTransFunc = multiprocTransFunc;
        this.pids = pids;
        this.solver = solver;
        this.mcm = mcm;
    }

    @Override
    public SafetyResult<S, A> check(final P prec) {
        final ExecutionGraphBuilder builder = new ExecutionGraphBuilder(tags);

        final List<Integer> initialWriteIds = new ArrayList<>();

        final Map<Integer, VarDecl<?>> vars = new LinkedHashMap<>();
        for (MemoryEvent initialWrite : initialWrites) {
            int i = builder.addInitialWrite(initialWrite.varId());
            vars.put(i, initialWrite.var());
            initialWriteIds.add(i);
        }

        List<List<Integer>> events = new ArrayList<>();


        for (final int pid : pids) {
            Map<MemoryEvent, Integer> reads = new LinkedHashMap<>();
            List<Integer> list = new ArrayList<>();
            events.add(list);
            final Collection<? extends S> initStates = multiprocInitFunc.getInitStates(pid, prec);
            checkState(initStates.size() == 1);
            int lastId = 0;
            S state = null;
            for (final S initState : initStates) { // will only execute once
                state = initState;
            }
            while(true) {
                final Collection<A> enabledActionsFor = multiprocLTS.getEnabledActionsFor(pid, state);
                if (enabledActionsFor.size() == 0) break;
                checkState(enabledActionsFor.size() == 1);
                for (final A a : enabledActionsFor) { // will execute only once
                    final Collection<MemoryEvent> memoryEventsOf = memoryEventProvider.getMemoryEventsOf(state, a);
                    for (MemoryEvent memoryEvent : memoryEventsOf) {
                        lastId = switch (memoryEvent.type()) {
                            case READ -> builder.addRead(pid, memoryEvent.varId(), lastId, Set.of());
                            case WRITE -> builder.addWrite(pid, memoryEvent.varId(), lastId, Set.of());
                            case FENCE -> builder.addFence(pid, lastId, Set.of());
                        };

                        if (memoryEvent.type() == READ) reads.put(memoryEvent, lastId);
                        else if (memoryEvent.type() == WRITE) {
                            for (MemoryEvent read : reads.keySet()) {
                                if (memoryEvent.dependencies().contains(read.localVar())) {
                                    builder.addDependency(reads.get(read), lastId);
                                }
                            }
                        }

                        if (memoryEvent.var() != null) vars.put(lastId, memoryEvent.var());
                        list.add(lastId);
                    }
                    final Collection<? extends S> succStates = multiprocTransFunc.getSuccStates(pid, state, a, prec);
                    checkState(succStates.size() == 1);
                    for (final S succState : succStates) { // will execute only once
                        state = succState;
                    }
                }
            }
        }

        final ExecutionGraph executionGraph = new ExecutionGraph(builder, mcm, solver);
        Set<ConstDecl<?>> vars1 = new LinkedHashSet<>();
        for (Expr<BoolType> assertion : solver.getAssertions()) {
            vars1.addAll(ExprUtils.getConstants(assertion));
        }
        for (ConstDecl<?> varDecl : vars1) {
//            System.out.println("(declare-fun " + varDecl.getName() + " () Bool)");
        }
        for (Expr<BoolType> assertion : solver.getAssertions()) {
            System.out.println("(assert " + assertion + " )");
        }

        Collection<Map<Decl<?>, LitExpr<?>>> solutions = new ArrayList<>();

        executionGraph.print(vars);
        int i = 0;
        while(executionGraph.nextSolution(solutions)) {
            executionGraph.print(vars);
            System.out.println("====");
            i++;
        }
        executionGraph.reset();

        System.out.println("Found " + i + " distinct executions.");

        final ExecutionGraphVisualizer visualizer = new ExecutionGraphVisualizer(executionGraph, solutions, events, initialWriteIds);
        Thread t = new Thread(visualizer);
        t.start();
        try {
            t.join();
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }

        return null;
    }
}
