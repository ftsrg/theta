/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.ansd;

import hu.bme.mit.delta.collections.IntSetView;
import hu.bme.mit.delta.java.mdd.MddNode;

/**
 * Represents a sub-state space of the system under analysis. Instances of this type have some sort
 * of a decision diagram node underneath to represent the reachable substates.
 *
 * @author Vince Molnar
 */
public interface StateSpaceInfo {
    /**
     * Gets the trace info associated with the currently processed variable.
     *
     * @return The current trace info.
     */
    Object getTraceInfo();

    default <T> T getTraceInfo(Class<T> typeToken) {
        return typeToken.cast(getTraceInfo());
    }

    /**
     * Returns true if the underlying component is known to have specific reachable states, false if
     * its state space is undefined, that is, it can be in any state.
     *
     * @return True if the underlying component has specific reachable states, false if its state
     *     space is undefined.
     */
    public boolean hasInfiniteStates();

    /**
     * Gets the local states of the underlying component that are contained in the current sub-state
     * space. <b>Returns {@code null} if {@link #hasInfiniteStates()} returns false.</b>
     *
     * @return The local states of the underlying component that are contained in the current
     *     sub-state space or {@code null} if the state space is undefined.
     */
    public IntSetView getLocalStateSpace();

    // TODO: possible tweaking. When is it worth it to traverse the MDD and collect
    // the actual states instead of relying on the domain registry?

    /**
     * Gets the local states of {@code someLowerComponent} that are contained in the current
     * sub-state space. <b>Returns {@code null} if the state space of {@code someLowerComponent} is
     * undefined.</b>
     *
     * @return The local states of the underlying component that are contained in the current
     *     sub-state space or {@code null} if the state space is undefined.
     */
    public StateSpaceInfo getLocalStateSpace(Object someLowerComponent);

    public MddNode toStructuralRepresentation();
}
