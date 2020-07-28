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
package hu.bme.mit.theta.xcfa.algorithm;

import hu.bme.mit.theta.xcfa.algorithm.util.DfsNodeInterface;
import hu.bme.mit.theta.xcfa.expl.ExplState;
import hu.bme.mit.theta.xcfa.expl.Transition;

import javax.annotation.Nullable;
import java.util.Collection;
import java.util.Iterator;

abstract class DfsNodeBase implements DfsNodeInterface {
    private final ExplState state;
    private final Transition lastTransition;
    private Iterator<Transition> nextTransition;
    protected DfsNodeBase(ExplState state, @Nullable Transition lastTransition,
                        Collection<Transition> outgoingTransitions) {
        this.state = state;
        this.lastTransition = lastTransition;
        nextTransition = outgoingTransitions.iterator();
    }

    public ExplState getState() {
        return state;
    }

    public Transition getLastTransition() {
        return lastTransition;
    }

    protected void resetWithTransitions(Collection<Transition> newOutgoingTransitions) {
        nextTransition = newOutgoingTransitions.iterator();
    }

    public boolean hasChild() {
        return isSafe() &&
                !state.getSafety().finished &&
                nextTransition.hasNext();
    }

    public boolean isSafe() {
        return state.getSafety().safe;
    }

    protected final Transition fetchNextTransition() {
        return nextTransition.next();
    }

    public abstract DfsNodeBase child();
}
