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
import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionBase;
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.LocalityUtils;
import hu.bme.mit.theta.xcfa.alt.expl.ProcessTransitions;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.HashSet;
import java.util.OptionalInt;

final class DynamicPOChecker extends XcfaChecker {

    private final IndexingUtil indexing = new IndexingUtil();

    DynamicPOChecker(XCFA xcfa, Config config) {
        super(xcfa, config);
        Preconditions.checkArgument(config.isPartialOrder(), "Partial order reduction but no partial order flag");
        Preconditions.checkArgument(config.optimizeLocals(), "Optimizing locals cannot be turned off " +
                "for DPOR (yet)");
        Preconditions.checkArgument(!config.discardAlreadyExplored(), "Already explored states cannot be " +
                "discarded when using Dynamic Partial Order Reduction.");
    }

    @Override
    protected void onNodePushed(DfsNodeBase node) {
        backtrack((DfsNode)node);
    }

    @Override
    protected DfsNodeBase initialNode(ImmutableExplState state) {
        return new DfsNode(state, null);
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
            Transition t = dfsStack.get(idx+1).getLastTransition();
            // TODO
            //noinspection OptionalGetWithoutIsPresent
            return get(idx).getAll().stream().filter(x->x.getProcess() == t.getProcess()).findAny().get();
        }

        /** get(i).lastTransition should probably not be used */
        DfsNode get(int idx) {
            Preconditions.checkArgument(minIndex() <= idx && idx <= maxIndex());
            return (DfsNode) dfsStack.get(idx);
        }

        /** Returns whether the transition is local, and we optimized on that fact,
         * meaning that we should not try to backtrack or find dependency.
         */
        private boolean isLocalTransitionOptimization(int idx) {
            return get(idx).isLocalOptimization();
        }
    }

    private boolean happensBefore( int i, int j) {
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

    private boolean happensBefore(int i, ProcessTransitions pt) {
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

    private OptionalInt findLastDependentCoenabled(ProcessTransitions p) {
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

    private boolean checkProcessWithEnabledTransitionHappeningBefore(ProcessTransitions q, int i, ProcessTransitions p) {
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

    private void backtrack(DfsNode lastNode) {
        // TODO rework loop logic
        // fill backtrack of older transitions...
        for (var p : lastNode.getAll()) {
            if (p.transitionStream().findAny().isEmpty())
                continue;
            var opti = findLastDependentCoenabled(p);
            if (opti.isEmpty())
                continue;
            int i = opti.getAsInt();
            // E is enabled transitions in
            Collection<ProcessTransitions> E = new HashSet<>();
            DfsNode oldState = indexing.get(i);
            for (var q: oldState.getAll()) {
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
    private static final class DfsNode extends DfsNodeBase {

        /**
         * Is it *initialized* with localOptimization?
         * This can change, however.
         */
        private final boolean initedLocalOptimization;

        private DfsNode(ImmutableExplState state, @Nullable ExecutableTransitionBase lastTransition) {
            super(state, lastTransition);

            var local = LocalityUtils.findAnyEnabledLocalProcessTransition(state);
            if (local.isPresent()) {
                // if a local transition set was found at a process ->
                // no backtracking, etc. is needed.
                initedLocalOptimization = true;
                push(local.get());
            } else {
                initedLocalOptimization = false;
                var y = getAll().stream().filter( // has an enabled transition
                        ProcessTransitions::hasAnyEnabledTransition
                ).findAny(); // any enabled will do
                y.ifPresent(this::push);
                // if empty, we are in final location or deadlock, but it's not a problem.
            }
        }

        boolean isLocalOptimization() {
            return initedLocalOptimization && !isExpanded();
        }

        @Override
        public DfsNodeBase nodeFrom(ImmutableExplState state, ExecutableTransitionBase lastTransition) {
            return new DfsNode(state, lastTransition);
        }
    }
}
