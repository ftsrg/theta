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
import hu.bme.mit.theta.xcfa.alt.algorithm.util.Tracer;
import hu.bme.mit.theta.xcfa.alt.expl.ExplState;
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.LocalityUtils;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

/**
 * An explicit checker traversing every possible ordering of an XCFA state.
 * Supports only zero-initialized values (because of how ExplState works).
 */
final class ExplicitChecker extends XcfaChecker{
    private final Set<ExplState> exploredStates = new HashSet<>();
    private final Set<ExplState> stackedStates = new HashSet<>();
    private final Stack<DfsNode> dfsStack = new Stack<>();

    private boolean discardAlreadyExploredStates() {
        return config.discardAlreadyExplored();
    }

    /**
     * Checking whether a state is checked is needed for detecting cylces,
     * these are needed by some algorithms.
     * Also, for checking infinite loops!
     */
    private boolean rememberStackedStates() {
        return true;
    }

    ExplicitChecker(XCFA xcfa, Config config) {
        super(xcfa,config);
    }

    /** Pushes the node to the stack if not explored before */
    private void tryPushNode(DfsNode node) {
        ImmutableExplState state = node.getState();
        debugPrint(state);
        if (discardAlreadyExploredStates()) {
            if (exploredStates.contains(state)) {
                return;
            }
            exploredStates.add(state);
        }
        if (rememberStackedStates()) {
            stackedStates.add(state);
        }
        dfsStack.push(node);
    }

    private void popNode(DfsNode s0) {
        ExplState state = dfsStack.pop().getState();
        if (rememberStackedStates()) {
            stackedStates.remove(state);
        }
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
                var child = node.child();
                // first check for cycles, then check for explored states
                if (rememberStackedStates() && stackedStates.contains(child.getState())) {
                    node.expand();
                    // expand, do not remove, and retry
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

    private final class DfsNode extends DfsNodeBase {

        boolean local = false;

        /**
         * Returns a process with only local transitions or every transition
         */
        Collection<ImmutableExplState.ExecutableTransition> oneLocalOrEveryTransition(ImmutableExplState state) {
            if (!config.optimizeLocals())
                return null;
            Optional<List<ImmutableExplState.ExecutableTransition>> t = LocalityUtils.findAnyEnabledLocalProcessTransition(state).map(
                    p->p.enabledStream().map(state::transitionFrom).collect(Collectors.toUnmodifiableList())
            );
            if (t.isPresent()) {
                assert !t.get().isEmpty();
                return t.get();
            }
            return null;
        }

        DfsNode(ImmutableExplState state, @Nullable Transition lastTransition) {
            super(state, lastTransition, state.getEnabledTransitions());
            var l = oneLocalOrEveryTransition(state);
            if (l != null) {
                local = true;
                resetWithTransitions(l);
            }
        }

        @Override
        public DfsNode child() {
            // TODO do not copy to new immutable state when there is only one transition?
            var t = fetchNextTransition();
            return new DfsNode(t.execute(), t);
        }

        void expand() {
            if (local) {
                local = false;
                resetWithTransitions(getState().getEnabledTransitions());
            }
        }
    }
}
