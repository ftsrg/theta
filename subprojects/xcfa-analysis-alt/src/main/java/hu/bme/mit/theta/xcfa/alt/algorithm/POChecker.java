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
package hu.bme.mit.theta.xcfa.alt.algorithm;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionBase;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionUtils;
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.ProcessTransitions;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;
import hu.bme.mit.theta.xcfa.alt.expl.TransitionUtils;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class POChecker extends XcfaChecker {

    private static class AmpleSetFactory {
        // pre(Pi)
        private final Collection<ProcessTransitions> allTransitionsByProcess;

        public AmpleSetFactory(XCFA xcfa) {
            allTransitionsByProcess = TransitionUtils.getProcessTransitions(xcfa);
        }

        private void collectDependingProcesses(ProcessTransitions t, Collection<XCFA.Process> alreadyProcessed,
                                               Collection<XCFA.Process> result) {
            t.transitionStream().forEach(tr->collectDependingProcesses(tr, alreadyProcessed, result));
        }

        private void collectDependingProcesses(Transition t, Collection<XCFA.Process> alreadyProcessed,
                                               Collection<XCFA.Process> result) {
            for (var x : allTransitionsByProcess) {
                if (alreadyProcessed.contains(x.getProcess())) {
                    continue;
                }
                if (result.contains(x.getProcess())) {
                    continue;
                }
                if (x.getProcess() == t.getProcess()) {
                    continue;
                }
                if (DependencyUtils.depends(x, t)) {
                    result.add(x.getProcess());
                }
            }
        }

        // input is a non empty set of enabled transitions
        private Collection<XCFA.Process> collectAmpleSet(ImmutableExplState state) {
            HashSet<XCFA.Process> ampleSet = new HashSet<>();
            HashSet<XCFA.Process> notYetProcessed = new HashSet<>();

            Collection<ProcessTransitions> enabledProcesses = TransitionUtils.getProcessTransitions(state).stream()
                    .filter(ProcessTransitions::hasAnyEnabledTransition)
                    .collect(Collectors.toUnmodifiableList());

            // add a transition
            ProcessTransitions first = enabledProcesses.iterator().next();
            notYetProcessed.add(first.getProcess());

            // add dependencies transitively
            while (!notYetProcessed.isEmpty()) {
                XCFA.Process toBeProcessed = notYetProcessed.iterator().next();
                ampleSet.add(toBeProcessed);

                notYetProcessed.remove(toBeProcessed);
                for (ProcessTransitions enabledProcess : enabledProcesses) {
                    collectDependingProcesses(enabledProcess, ampleSet, notYetProcessed);
                }

                // Add disabled transitions' dependencies, which may activate the transition.
                // More precisely: all processes' transitions that may enable this disabled transition.
                // Look at partialorder-test.xcfa for more information
                for (ProcessTransitions enabledProcess : enabledProcesses) {
                    enabledProcess.disabledStream()
                            .forEach(
                                tr -> collectDependingProcesses(tr, ampleSet, notYetProcessed)
                            );
                }
            }
            return ampleSet;
        }

        // Does not contain the logic of C3 about cycles, they are handled in the DFS
        public Collection<XCFA.Process> returnAmpleSet(ImmutableExplState expl) {
            Collection<ExecutableTransitionBase> enabled = ExecutableTransitionUtils.getExecutableTransitions(expl)
                    .collect(Collectors.toUnmodifiableList());
            if (enabled.isEmpty()) {
                return Collections.emptySet();
            }
            return collectAmpleSet(expl);
        }
    }

    POChecker(XCFA xcfa, Config config) {
        super(xcfa,config);
    }

    @Override
    protected void onNodePushed(DfsNodeBase node) {
        //
    }

    @Override
    protected DfsNodeBase initialNode(ImmutableExplState state) {
        return new DfsNode(state, null);
    }

    private final class DfsNode extends DfsNodeBase {

        boolean optimized = true;

        private Stream<ProcessTransitions> collectTransitions(ImmutableExplState state, Collection<XCFA.Process> processes) {
            return TransitionUtils.getProcessTransitions(state).stream()
                    .filter(x->processes.contains(x.getProcess()));
        }

        DfsNode(ImmutableExplState state, @Nullable Transition lastTransition) {
            super(state, lastTransition);
            collectTransitions(state,
                    new AmpleSetFactory(xcfa).returnAmpleSet(state)
            ).forEach(this::push);
        }

        @Override
        public DfsNodeBase nodeFrom(ImmutableExplState state, ExecutableTransitionBase lastTransition) {
            return new DfsNode(state, lastTransition);
        }
    }

}
