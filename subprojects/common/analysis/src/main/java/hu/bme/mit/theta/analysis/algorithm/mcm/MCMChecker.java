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
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.Solver;

import java.util.*;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkState;

public class MCMChecker<S extends State, A extends Action, P extends Prec> implements SafetyChecker<S, A, P> {
    private final MemoryEventProvider<A> memoryEventProvider;
    private final MultiprocLTS<S, A> multiprocLTS;
    private final MultiprocInitFunc<S, P> multiprocInitFunc;
    private final MultiprocTransFunc<S, A, P> multiprocTransFunc;
    private final Collection<Integer> pids;
    private final Collection<String> tags;
    private final Solver solver;
    private final MCM mcm;

    public MCMChecker(
            final MemoryEventProvider<A> memoryEventProvider,
            final MultiprocLTS<S, A> multiprocLTS,
            final MultiprocInitFunc<S, P> multiprocInitFunc,
            final MultiprocTransFunc<S, A, P> multiprocTransFunc,
            final Collection<Integer> pids,
            final Collection<String> tags,
            final Solver solver,
            final MCM mcm) {
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

        final Map<Integer, VarDecl<?>> vars = new LinkedHashMap<>();

        for (final int pid : pids) {
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
                    final Collection<MemoryEvent> memoryEventsOf = memoryEventProvider.getMemoryEventsOf(a);
                    for (final MemoryEvent memoryEvent : memoryEventsOf) {
                        lastId = switch (memoryEvent.getType()) {
                            case READ -> builder.addRead(pid, memoryEvent.getVarId(), lastId, Set.of());
                            case WRITE -> builder.addWrite(pid, memoryEvent.getVarId(), lastId, Set.of());
                            case FENCE -> builder.addFence(pid, lastId, Set.of());
                        };
                        if(memoryEvent.getVar() != null) vars.put(lastId, memoryEvent.getVar());
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
//            System.out.println("(assert " + assertion + " )");
        }

//        executionGraph.print(vars);
        while(executionGraph.nextSolution()) {
            executionGraph.print(vars);
            System.out.println("====");
        }
        executionGraph.reset();
//        executionGraph.print();

        return null;
    }
}
