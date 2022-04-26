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

import java.util.Collection;

import static com.google.common.base.Preconditions.checkState;

public class MCMChecker<S extends State, A extends Action, P extends Prec> implements SafetyChecker<S, A, P> {
    private final MemoryEventProvider<A> memoryEventProvider;
    private final MultiprocLTS<S, A> multiprocLTS;
    private final MultiprocInitFunc<S, P> multiprocInitFunc;
    private final MultiprocTransFunc<S, A, P> multiprocTransFunc;
    private final Collection<Integer> pids;
    private final ExecutionGraph executionGraph;

    public MCMChecker(
            final MemoryEventProvider<A> memoryEventProvider,
            final MultiprocLTS<S, A> multiprocLTS,
            final MultiprocInitFunc<S, P> multiprocInitFunc,
            final MultiprocTransFunc<S, A, P> multiprocTransFunc,
            final Collection<Integer> pids) {
        this.memoryEventProvider = memoryEventProvider;
        this.multiprocLTS = multiprocLTS;
        this.multiprocInitFunc = multiprocInitFunc;
        this.multiprocTransFunc = multiprocTransFunc;
        this.pids = pids;
        executionGraph = new ExecutionGraph();
    }

    @Override
    public SafetyResult<S, A> check(final P prec) {
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

        executionGraph.print();

        return null;
    }
}
