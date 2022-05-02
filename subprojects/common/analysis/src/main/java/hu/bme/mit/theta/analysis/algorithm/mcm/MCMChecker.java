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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.*;

public class MCMChecker<S extends State, A extends Action, P extends Prec> implements SafetyChecker<S, A, P> {
    private final MemoryEventProvider<A> memoryEventProvider;
    private final MultiprocLTS<S, A> multiprocLTS;
    private final MultiprocInitFunc<S, P> multiprocInitFunc;
    private final MultiprocTransFunc<S, A, P> multiprocTransFunc;
    private final Collection<Integer> pids;
    private final Solver solver;
    private final MCM mcm;

    public MCMChecker(
            final MemoryEventProvider<A> memoryEventProvider,
            final MultiprocLTS<S, A> multiprocLTS,
            final MultiprocInitFunc<S, P> multiprocInitFunc,
            final MultiprocTransFunc<S, A, P> multiprocTransFunc,
            final Collection<Integer> pids,
            final Solver solver,
            final MCM mcm) {
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
        final ExecutionGraph executionGraph = new ExecutionGraph();

        for (final int pid : pids) {
            final Collection<? extends S> initStates = multiprocInitFunc.getInitStates(pid, prec);
            checkState(initStates.size() == 1);
            int lastId = -1;
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
                            case READ -> executionGraph.addRead(pid, memoryEvent.getVarId(), lastId);
                            case WRITE -> executionGraph.addWrite(pid, memoryEvent.getVarId(), lastId);
                            case FENCE -> executionGraph.addFence(pid, lastId);
                        };
                    }
                    final Collection<? extends S> succStates = multiprocTransFunc.getSuccStates(pid, state, a, prec);
                    checkState(succStates.size() == 1);
                    for (final S succState : succStates) { // will execute only once
                        state = succState;
                    }
                }
            }
        }

        EncodedRelationWrapper encodedRelationWrapper = new EncodedRelationWrapper(solver);
        Collection<ConstDecl<BoolType>> rfConsts = executionGraph.encode(mcm, encodedRelationWrapper);

        final List<String> toDraw = List.of("po", "co", "rf");

        while(solver.check().isSat()) {
            System.out.println("digraph G{");
            final List<Expr<BoolType>> subexprs = new ArrayList<>();
            solver.getModel().toMap().entrySet().stream().filter(e -> e.getValue().equals(True())).forEach(e -> {
                String[] constDecl = e.getKey().getName().split("_");
                if(constDecl.length != 3) throw new RuntimeException("Wrong format for constant");

                if(toDraw.contains(constDecl[0])) {
                    System.out.print(constDecl[1] + " -> " + constDecl[2]);
                    if (!constDecl[0].equals("po")) {
                        System.out.print(" [label=\"" + constDecl[0] + "\",color=grey,constraint=false]");
                    }
                    System.out.println(";");
                }

                if(rfConsts.contains(e.getKey())) {
                    subexprs.add((Expr<BoolType>) e.getKey().getRef());

                }
            });
            solver.add(Not(And(subexprs)));
            System.out.println("}");
            System.out.println("");
            System.out.println("=====");
            System.out.println("");
        }

        return solver.check() == SolverStatus.UNSAT ? SafetyResult.safe(null) : SafetyResult.unsafe(null, null);
    }
}
