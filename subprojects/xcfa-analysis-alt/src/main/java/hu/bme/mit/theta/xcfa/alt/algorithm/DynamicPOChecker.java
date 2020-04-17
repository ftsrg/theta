/*
 * Copyright 2019 Budapest University of Technology and Economics
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package hu.bme.mit.theta.xcfa.alt.algorithm;

import com.google.common.base.Preconditions;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.algorithm.util.DfsNodeInterface;
import hu.bme.mit.theta.xcfa.alt.algorithm.util.Tracer;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransition;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionForImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionUtils;
import hu.bme.mit.theta.xcfa.alt.expl.ExplState;
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.LocalityUtils;
import hu.bme.mit.theta.xcfa.alt.expl.ProcessTransitions;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;
import hu.bme.mit.theta.xcfa.alt.expl.TransitionUtils;

import javax.annotation.Nullable;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.HashSet;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

/** TODO Currently not working */
public class DynamicPOChecker {
    private final XCFA xcfa;
    private final boolean debug;
    private final Set<ExplState> exploredStates = new HashSet<>();
    private final Set<ExplState> stackedStates = new HashSet<>();
    private final Stack<DfsNode> dfsStack = new Stack<>();

    public DynamicPOChecker(XCFA xcfa) {
        this(xcfa, false);
    }

    public DynamicPOChecker(XCFA xcfa, boolean debug) {
        this.xcfa = xcfa;
        this.debug = debug;
    }

    private static void debugPrint(ImmutableExplState s, boolean debug) {
        if (!debug)
            return;
        System.out.println(s);
        System.out.println("Enabled transitions:");
        for (var tr : s.getEnabledTransitions()) {
            System.out.println(tr);
        }
        System.out.println();
    }

    /** Pushes the node to the stack if not explored before */
    private void tryPushNode(DfsNode node) {

        ImmutableExplState state = node.getState();
        if (stackedStates.contains(state)) {
            throw new UnsupportedOperationException("Dynamic partial order checker does not support infinite loops.");
        }
        if (exploredStates.contains(state)) {
            return;
        }

        backtrack(node);

        debugPrint(state, debug);
        stackedStates.add(state);
        exploredStates.add(state);
        dfsStack.push(node);
    }

    private void popNode(DfsNode s0) {
        ExplState state = dfsStack.pop().getState();
        stackedStates.remove(state);
        assert(state.equals(s0.getState()));
    }

    /**
     * SafetyResult should be always unsafe OR finished.
     */
    public SafetyResult<ExplState, Transition> check() {

        tryPushNode(new DfsNode(ImmutableExplState.initialState(xcfa), null));

        while (!dfsStack.empty()) {
            DfsNode node = dfsStack.peek();
            if (node.hasChild()) {
                tryPushNode(node.child());
            } else {
                if (!node.isSafe()) {
                    return Tracer.unsafe(dfsStack);
                }
                popNode(node);
            }
        }
        return Tracer.safe();
    }

    private class IndexingUtil {

        int minIndex() {
            return 1;
        }

        /** The current state is not needed to be processed by backtracking */
        int maxIndex() {
            return dfsStack.size()-2; // TODO ?
        }

        ExecutableTransition getTransition(int idx) {
            Preconditions.checkArgument(minIndex() <= idx && idx <= maxIndex());
            return dfsStack.get(idx+1).lastTransition;
        }

        DfsNode get(int idx) {
            return dfsStack.get(idx);
        }

        boolean isInteresting(int idx) {
            return !get(idx).localProcessTransition;
        }
    }

    public boolean happensBefore(Transition tr1, int i, Transition tr2, int j) {
        Preconditions.checkArgument(indexing.getTransition(i) == tr1);
        Preconditions.checkArgument(indexing.getTransition(j) == tr2);
        Preconditions.checkArgument(i <= j);
        if (i == j)
            return true;
        if (DependencyUtils.depends(tr1, tr2))
            return true;
        for (int k = i+1; k < j; k++) {
            if (happensBefore(tr1, i, indexing.getTransition(k), k) &&
                    happensBefore(indexing.getTransition(k), k, tr2, j))
                return true;
        }
        return false;

    }
    public boolean happensBefore(Transition tr, int i, ProcessTransitions pt) {
        Preconditions.checkArgument(indexing.getTransition(i) == tr);
        if (tr.getProcess() == pt.process)
            return true;
        for (int k = i+1; k <= indexing.maxIndex(); k++) {
            if (happensBefore(tr, i, indexing.getTransition(k), k)
                    && indexing.getTransition(k).getProcess() == pt.process)
                return true;
        }
        return false;
    }

    private final IndexingUtil indexing = new IndexingUtil();

    void backtrack(DfsNode lastNode) {
        // fill backtrack of older transitions...
        for (var currentProcess : lastNode.all) { // p in the paper
            // transition i
            int i;
            boolean found = false;
            for (i = indexing.maxIndex(); i >= indexing.minIndex(); i--) {
                if (!indexing.isInteresting(i))
                    continue;
                Transition tr = indexing.getTransition(i);
                if (DependencyUtils.depends(currentProcess, tr) &&
                        CoenabledUtils.coenabled(currentProcess, tr) &&
                        happensBefore(tr, i, currentProcess)) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                continue;
            }
            // E is enabled transitions in
            Collection<ProcessTransitions> E = new HashSet<>();
            DfsNode oldState = indexing.get(i);
            for (var oldProcess: oldState.all) { // q in the paper
                // q is enabled in the old state
                if (oldProcess.enabledStream().findAny().isEmpty()) {
                    continue;
                }
                // q=p
                found = false;
                if (oldProcess.process == currentProcess.process) {
                    E.add(oldProcess);
                    found = true;
                }

                // or there exists a transition which depend on those i and p

                for (int j = i+1; !found && j <= indexing.maxIndex(); j++) {
                    if (!indexing.isInteresting(j))
                        continue;
                    ExecutableTransition t = indexing.getTransition(j);
                    if (t.getProcess() == oldProcess.process &&
                            happensBefore(t, j, currentProcess)
                    ) {
                        found = true;
                    }
                }
                if (found)
                    E.add(oldProcess);
            }
            if (!E.isEmpty()) {
                E.forEach(oldState::push);
            } else {
                oldState.expand();
            }
            break;
        }
    }

    /**
     * If there is a local processTransition with at least one transition enabled, then it consists of all the
     *      enabled ones. (with the help of LocalityUtils)
     * (ProcessTransition is all the transitions of one process)
     * If there is no local pt, then we need to select a pt of our choice.
     * If there is a dependent transition later, we need to add that to the backtrack set.
     */
    private static final class DfsNode implements DfsNodeInterface {

        /** Transitions that need to be processed. */
        private final Queue<ExecutableTransitionForImmutableExplState> todo;
        private final Collection<ProcessTransitions> all;

        private final Set<ProcessTransitions> backtrack = new HashSet<>();
        private final ImmutableExplState state;
        private final ExecutableTransition lastTransition;
        private final boolean localProcessTransition;

        private Optional<Collection<ExecutableTransitionForImmutableExplState>> localProcessTransition(ImmutableExplState state) {
            var p = LocalityUtils.findAnyEnabledLocalTransition(state);
            return p.map(enabledTransitions ->
                    enabledTransitions.stream()
                            .map(state::transitionFrom)
                            .collect(Collectors.toUnmodifiableSet()));
        }

        private void push(ProcessTransitions pt) {
            Preconditions.checkState(!localProcessTransition);
            if (backtrack.contains(pt))
                return;
            backtrack.add(pt);
            ExecutableTransitionUtils.streamExecutableTransitions(state, pt.stream())
                    .map(state::transitionFrom).forEach(todo::add);
        }

        private DfsNode(ImmutableExplState state, @Nullable ExecutableTransition lastTransition) {
            this.state = state;
            this.lastTransition = lastTransition;
            all = TransitionUtils.getProcessTransitions(state);
            var local = localProcessTransition(state);
            todo = new ArrayDeque<>();
            if (local.isPresent()) {
                localProcessTransition = true;
                todo.addAll(local.get());
            } else {
                localProcessTransition = false;
                // There could be no transitions, we are in a deadlock or final location
                var y = all.stream().filter( // has an enabled transition
                        pt -> pt.enabledStream().findAny().isPresent()
                ).findAny(); // any enabled will do
                y.ifPresent(this::push);
                assert y.isEmpty() == todo.isEmpty();
            }

        }

        /** fully expand */
        private void expand() {
            for (var processTransitions : all) {
                if (processTransitions.enabledStream().findAny().isEmpty())
                    continue;
                push(processTransitions);
            }
        }

        public DfsNode child() {
            ExecutableTransition t = fetchNextTransition();
            return new DfsNode(((ExecutableTransitionForImmutableExplState)t).execute(), t);
        }

        private ExecutableTransition fetchNextTransition() {
            return todo.poll();
        }

        @Override
        public ImmutableExplState getState() {
            return state;
        }

        @Override
        public Transition getLastTransition() {
            return lastTransition;
        }

        public boolean isSafe() {
            return state.getSafety().isSafe();
        }

        public boolean hasChild() {
            return !todo.isEmpty();
        }
    }
}
