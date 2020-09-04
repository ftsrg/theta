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

import hu.bme.mit.theta.xcfa.alt.algorithm.util.DfsNodeInterface;
import hu.bme.mit.theta.xcfa.alt.expl.ExecutableTransitionBase;
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.ProcessTransitions;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;
import hu.bme.mit.theta.xcfa.alt.expl.TransitionUtils;

import javax.annotation.Nullable;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

abstract class DfsNodeBase implements DfsNodeInterface {
    private final ImmutableExplState state;
    private final Transition lastTransition;
    private final Queue<ImmutableExplState.ExecutableTransition> todo;

    private final Collection<ProcessTransitions> all;
    private Set<ProcessTransitions> addedTransitions;
    private boolean expanded = false;
    protected DfsNodeBase(ImmutableExplState state, @Nullable Transition lastTransition) {
        this.state = state;
        this.lastTransition = lastTransition;
        all = TransitionUtils.getProcessTransitions(state);
        todo = new ArrayDeque<>();
        addedTransitions = new HashSet<>();
    }

    public boolean isExpanded() {
        return expanded;
    }

    public ImmutableExplState getState() {
        return state;
    }

    public Transition getLastTransition() {
        return lastTransition;
    }

    public boolean hasChild() {
        return !state.getSafety().isFinished() &&
               !todo.isEmpty();
    }

    public boolean isSafe() {
        return state.getSafety().isSafe();
    }

    public boolean isFinished() {
        return state.getSafety().isFinished();
    }

    protected final ImmutableExplState.ExecutableTransition fetchNextTransition() {
        return todo.poll();
    }

    public abstract DfsNodeBase nodeFrom(ImmutableExplState state, ExecutableTransitionBase lastTransition);

    public DfsNodeBase child() {
        var t = fetchNextTransition();
        return nodeFrom(t.execute(), t);
    }


    public Collection<ProcessTransitions> getAll() {
        return Collections.unmodifiableCollection(all);
    }

    @Override
    public String toString() {
        return "DfsNodeBase{" +
                "state=" + state +
                ", lastTransition=" + lastTransition +
                '}';
    }

    public void push(ProcessTransitions processTransitions) {
        if (addedTransitions.contains(processTransitions))
            return;
        addedTransitions.add(processTransitions);
        processTransitions.enabledStream().map(state::transitionFrom).forEach(todo::add);
    }

    public void expand() {
        if (expanded) {
            return;
        }
        expanded = true;

        var newOutgoingTransitions = new HashSet<>(all);
        newOutgoingTransitions.removeAll(addedTransitions);

        // equivalent to all.forEach(this::push);
        addedTransitions = new HashSet<>(all);
        newOutgoingTransitions.stream()
                .flatMap(ProcessTransitions::enabledStream)
                .map(state::transitionFrom)
                .forEach(todo::add);
    }
}
