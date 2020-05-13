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
import hu.bme.mit.theta.xcfa.alt.expl.ImmutableExplState;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;
import javax.annotation.Nullable;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

abstract class DfsNodeBase implements DfsNodeInterface {
    private final ImmutableExplState state;
    private final Transition lastTransition;
    private Iterator<ImmutableExplState.ExecutableTransition> nextTransition;
    private final Set<ImmutableExplState.ExecutableTransition> processedTransitions = new HashSet<>();
    protected DfsNodeBase(ImmutableExplState state, @Nullable Transition lastTransition,
                          Collection<ImmutableExplState.ExecutableTransition> outgoingTransitions) {
        this.state = state;
        this.lastTransition = lastTransition;
        nextTransition = outgoingTransitions.iterator();
    }

    public ImmutableExplState getState() {
        return state;
    }

    public Transition getLastTransition() {
        return lastTransition;
    }

    protected void resetWithTransitions(Collection<ImmutableExplState.ExecutableTransition> newOutgoingTransitions) {
        newOutgoingTransitions = new HashSet<>(newOutgoingTransitions);
        newOutgoingTransitions.removeAll(processedTransitions);
        nextTransition = newOutgoingTransitions.iterator();
    }

    public boolean hasChild() {
        return !state.getSafety().isFinished() &&
                nextTransition.hasNext();
    }

    public boolean isSafe() {
        return state.getSafety().isSafe();
    }

    protected final ImmutableExplState.ExecutableTransition fetchNextTransition() {
        var p = nextTransition.next();
        processedTransitions.add(p);
        return p;
    }

    public abstract DfsNodeBase child();

    @Override
    public String toString() {
        return "DfsNodeBase{" +
                "state=" + state +
                ", lastTransition=" + lastTransition +
                '}';
    }

    public boolean isFinished() {
        return state.getSafety().isFinished();
    }
}
