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

import hu.bme.mit.theta.analysis.algorithm.SafetyChecker;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expl.ExplPrec;
import hu.bme.mit.theta.analysis.expl.ExplState;
import hu.bme.mit.theta.analysis.expl.ExplTransFunc;
import hu.bme.mit.theta.analysis.expr.ExprAction;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.solver.Solver;

import java.util.Collection;
import java.util.Map;

import static org.abego.treelayout.internal.util.Contract.checkState;

/**
 * This class contains the implementation of the reachability checker based on the Herd-style declarative algorithm
 * @param <S>   The state type used in the analysis
 * @param <A>   The action type used in the analysis
 * @param <P>   The explicit precision that contains the set of variables to track
 * @param <SID> The scope ID type
 * @param <PID> The process ID type
 */
public class MCMChecker<S extends ExplState, A extends ExprAction, P extends ExplPrec, SID, PID> implements SafetyChecker<S, A, P> {
    private final MemoryEventProvider<S, A, SID, PID> memoryEventProvider;
    private final ExplTransFunc transFunc;

    public MCMChecker(MemoryEventProvider<S, A, SID, PID> memoryEventProvider, final Solver solver) {
        this.memoryEventProvider = memoryEventProvider;
        transFunc = ExplTransFunc.create(solver);
    }

    @Override
    public SafetyResult<S, A> check(final P prec) {
        final ExecutionGraph<SID, PID> executionGraph = new ExecutionGraph<>();
        int uniqueCounter = 0;
        final Map<SID, Map<PID, Collection<S>>> initialStates = memoryEventProvider.getInitialStates();
        for (Map.Entry<SID, Map<PID, Collection<S>>> entry : initialStates.entrySet()) {
            final SID sid = entry.getKey();
            final Map<PID, Collection<S>> processes = entry.getValue();
            for (Map.Entry<PID, Collection<S>> e : processes.entrySet()) {
                final PID pid = e.getKey();
                ExecutionGraph.Node<SID, PID> lastNode = executionGraph.addNode("init", Tuple2.of(sid, pid), "init", "init");
                final Collection<S> states = e.getValue();
                checkState(states.size() == 1, "Only a single initial state per process is supported right now.");
                S state = states.stream().findAny().get();
                while(state != null) {
                    final Collection<MCMAction<A>> enabledActionsFor = memoryEventProvider.getEnabledActionsFor(state).get(sid).get(pid);
                    checkState(enabledActionsFor.size() <= 1, "Only deterministic programs are supported right now.");
                    if(enabledActionsFor.size() == 1) {
                        final MCMAction<A> action = enabledActionsFor.stream().findAny().get();
                        if(!action.isEmpty()) {
                            final MCMAction.MCMEventAction<A> eventAction = action.asEventAction();
                            final ExecutionGraph.Node<SID, PID> newNode = executionGraph.addNode(eventAction.getType() + uniqueCounter++, Tuple2.of(sid, pid), eventAction.getType(), eventAction.getTag());
                            executionGraph.addEdge(lastNode, newNode, "po");
                        }
                        final Collection<? extends ExplState> succStates = transFunc.getSuccStates(state, action.getAction(), ExplPrec.empty());
                        checkState(succStates.size() == 1, "Only deterministic programs are supported right now.");
                        //noinspection unchecked
                        state = (S) succStates.stream().findAny().get();
                    } else {
                        state = null;
                    }
                }
            }
        }

//        System.out.println(executionGraph);
        return null;
    }
}
