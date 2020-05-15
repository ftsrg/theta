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
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionBase;
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
import java.util.OptionalInt;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Stream;

public class DynamicPOChecker extends XcfaChecker {
    private final Set<ExplState> stackedStates = new HashSet<>();
    private final Stack<DfsNode> dfsStack = new Stack<>();

    private static Config defaultConfig() {
        var defaultConfig = new Config.Builder();
        defaultConfig.optimizeLocals = true;
        return defaultConfig.build();
    }

    DynamicPOChecker(XCFA xcfa, Config config) {
        super(xcfa, config);
        Preconditions.checkArgument(config.isPartialOrder(), "Partial order reduction but no partial order flag");
        Preconditions.checkArgument(config.optimizeLocals(), "Optimizing locals cannot be turned off " +
                "for DPOR (yet)");
        Preconditions.checkArgument(!config.discardAlreadyExplored(), "Already explored states cannot be " +
                "discarded when using Dynamic Partial Order Reduction.");
    }

    private static String debugIndentLevel = "";
    private static void pushDebug(DfsNode s, boolean debug) {
        if (!debug)
            return;
        nodeDebug(s);
        debugIndentLevel = debugIndentLevel + "  ";
    }

    private static void popDebug(DfsNode s, boolean debug) {
        if (!debug)
            return;
        debugIndentLevel = debugIndentLevel.substring(2);
        nodeDebug(s);
    }

    private static void nodeDebug(DfsNode s) {
        System.out.println(debugIndentLevel + "From:");
        System.out.println(debugIndentLevel + s.lastTransition);
        System.out.println(debugIndentLevel + "State:");
        System.out.println(debugIndentLevel + s.state.getProcessStates());
        System.out.println(debugIndentLevel + "Enabled transitions:");
        for (var tr : s.state.getEnabledTransitions()) {
            System.out.println(debugIndentLevel + tr);
        }
        System.out.println(debugIndentLevel);
    }

    /** Pushes the node to the stack if not explored before */
    private void tryPushNode(DfsNode node) {

        ImmutableExplState state = node.getState();
        // A state cannot be discarded when an equivalent state was already processed.
        // The path to finding the state is important
        // there are some tests, see DynamicPOCheckerCompletenessTest checking partialorder-test4.xcfa.
        //if (exploredStates.contains(state)) return;
        //exploredStates.add(state);

        stackedStates.add(state);
        dfsStack.push(node);

        backtrack(node);
    }

    private void popNode(DfsNode s0) {
        ExplState state = dfsStack.pop().getState();
        stackedStates.remove(state);
        popDebug(s0, config.debug());
        assert(state.equals(s0.getState()));
    }

    /**
     * SafetyResult should be always unsafe OR finished.
     */
    public SafetyResult<ExplState, Transition> check() {
        debugIndentLevel = "";

        tryPushNode(new DfsNode(ImmutableExplState.initialState(xcfa), null));

        while (!dfsStack.empty()) {
            DfsNode node = dfsStack.peek();
            if (node.hasChild()) {
                var child = node.child();
                if (stackedStates.contains(child.getState())) {
                    node.expand();
                } else {
                    tryPushNode(child);
                }
            } else {
                if (node.isFinished())
                    onFinished(dfsStack);
                if (!node.isSafe()) {
                    return Tracer.unsafe(dfsStack);
                }
                popNode(node);
            }
        }
        return Tracer.safe();
    }

    /**
     * This is a utility for converting between indexing in the paper and indexing here.
     * The paper uses an other indexing than what we use.
     */
    private class IndexingUtil {

        int minIndex() {
            return 0;
        }

        int maxIndex() {
            // The current state is not needed to be processed by backtracking
            return dfsStack.size()-2;
        }

        ProcessTransitions getProcessTransition(int idx) {
            Preconditions.checkArgument(minIndex() <= idx && idx <= maxIndex());
            Transition t = dfsStack.get(idx+1).lastTransition;
            //noinspection OptionalGetWithoutIsPresent
            return get(idx).all.stream().filter(x->x.getProcess() == t.getProcess()).findAny().get();
        }

        /** get(i).lastTransition should probably not be used */
        DfsNode get(int idx) {
            Preconditions.checkArgument(minIndex() <= idx && idx <= maxIndex());
            return dfsStack.get(idx);
        }

        /** Returns whether the transition is local, and we optimized on that fact,
         * meaning that we should not try to backtrack or find dependency.
         */
        boolean isLocalTransitionOptimization(int idx) {
            return get(idx).localProcessTransition;
        }
    }

    public boolean happensBefore( int i, int j) {
        ProcessTransitions tr1 = indexing.getProcessTransition(i);
        ProcessTransitions tr2 = indexing.getProcessTransition(j);
        Preconditions.checkArgument(i <= j);
        if (i == j)
            return true;
        if (DependencyUtils.depends(tr1, tr2))
            return true;
        for (int k = i+1; k < j; k++) {
            if (happensBefore(i, k) &&
                    happensBefore(k, j))
                return true;
        }
        return false;

    }
    public boolean happensBefore(int i, ProcessTransitions pt) {
        ProcessTransitions tr = indexing.getProcessTransition(i);
        if (tr.getProcess() == pt.getProcess())
            return true;
        for (int k = i+1; k <= indexing.maxIndex(); k++) {
            if (happensBefore(i, k)
                    && indexing.getProcessTransition(k).getProcess() == pt.getProcess())
                return true;
        }
        return false;
    }

    private final IndexingUtil indexing = new IndexingUtil();

    OptionalInt findLastDependentCoenabled(ProcessTransitions p) {
        for (int i = indexing.maxIndex(); i >= indexing.minIndex(); i--) {
            if (indexing.isLocalTransitionOptimization(i))
                continue;
            ProcessTransitions t = indexing.getProcessTransition(i);
            if (DependencyUtils.depends(p, t) && CoenabledUtils.coenabled(p, t) &&
                    !happensBefore(i, p))
                return OptionalInt.of(i);
        }
        return OptionalInt.empty();
    }

    boolean checkProcessWithEnabledTransitionHappeningBefore(ProcessTransitions q, int i, ProcessTransitions p) {
        if (p.getProcess() == q.getProcess())
            return true;
        for (int j = i+1; j < indexing.maxIndex(); j++) {
            if (indexing.isLocalTransitionOptimization(j))
                continue;
            if (q.getProcess() != indexing.getProcessTransition(j).getProcess())
                continue;
            if (happensBefore(j, p))
                return true;
        }
        return false;
    }

    void backtrack(DfsNode lastNode) {
        // fill backtrack of older transitions...
        for (var p : lastNode.all) {
            if (p.transitionStream().findAny().isEmpty())
                continue;
            var opti = findLastDependentCoenabled(p);
            if (opti.isEmpty())
                continue;
            int i = opti.getAsInt();
            // E is enabled transitions in
            Collection<ProcessTransitions> E = new HashSet<>();
            DfsNode oldState = indexing.get(i);
            for (var q: oldState.all) {
                // q must be enabled in the old state
                if (!q.hasAnyEnabledTransition()) {
                    continue;
                }

                if (checkProcessWithEnabledTransitionHappeningBefore(q, i, p)) {
                    E.add(q);
                }
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
    private final class DfsNode implements DfsNodeInterface {

        /** Transitions that need to be processed. Contains backtrack\completed */
        private final Queue<ImmutableExplState.ExecutableTransition> todo;
        /** Transitions grouped by the process in which they belong. */
        private final Collection<ProcessTransitions> all;

        /** The set of processes that need to be processed. Can change while traversing
         * the explicit state graph. */
        private final Set<ProcessTransitions> backtrack = new HashSet<>();
        private final ImmutableExplState state;
        private final ExecutableTransitionBase lastTransition;

        /**
         * Stores whether a local transition is executed next
         * (and hence no later backtracking will be needed).
         * */
        private boolean localProcessTransition;

        private void pushExecutableTransitions(Stream<ExecutableTransitionBase> transitionStream) {
            if (config.debug()) {
                System.out.println(debugIndentLevel + "From state ");
                System.out.println(debugIndentLevel + state.getProcessStates());
            }
            transitionStream.map(state::transitionFrom).forEach(
                    p -> {
                        todo.add(p);
                        if (config.debug()) {
                            System.out.println(debugIndentLevel + "Adding transition " + p);
                            System.out.println();
                        }
                    }
            );

        }

        /**
         * Adds a process to the backtrack set.
         * @param pt The process to be added to the backtrack set.
         */
        private void push(ProcessTransitions pt) {
            Preconditions.checkState(!localProcessTransition);
            if (backtrack.contains(pt))
                return;

            backtrack.add(pt);
            pushExecutableTransitions(pt.enabledStream());
        }

        private DfsNode(ImmutableExplState state, @Nullable ExecutableTransitionBase lastTransition) {
            this.state = state;
            this.lastTransition = lastTransition;

            pushDebug(this, config.debug());

            all = TransitionUtils.getProcessTransitions(state);
            var local = LocalityUtils.findAnyEnabledLocalProcessTransition(state);
            todo = new ArrayDeque<>();
            if (local.isPresent()) {
                // if a local transition set was found at a process ->
                // no backtracking, etc. is needed.
                localProcessTransition = true;
                pushExecutableTransitions(local.get().enabledStream());
            } else {
                localProcessTransition = false;
                var y = all.stream().filter( // has an enabled transition
                        ProcessTransitions::hasAnyEnabledTransition
                ).findAny(); // any enabled will do
                y.ifPresent(this::push);
                assert y.isEmpty() == todo.isEmpty();
                // if empty, we are in final location or deadlock, but it's not a problem.
            }

        }

        /** fully expand node. */
        private void expand() {
            localProcessTransition = false;
            all.stream().filter(ProcessTransitions::hasAnyEnabledTransition)
                    .forEach(this::push);
        }

        public DfsNode child() {
            ExecutableTransitionBase t = fetchNextTransition();
            return new DfsNode(((ImmutableExplState.ExecutableTransition)t).execute(), t);
        }

        private ExecutableTransitionBase fetchNextTransition() {
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

        public boolean isFinished() {
            return state.getSafety().isFinished();
        }
    }
}
