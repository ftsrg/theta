/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis;

import java.util.Collection;

/**
 * Common interface for Labeled Transition Systems (LTS). An LTS can provide
 * enabled actions for a given state.
 */
@FunctionalInterface
public interface LTS<S extends State, A extends Action> {

    /**
     * Gets the enabled actions for a given state.
     *
     * @param state the state whose enabled actions we would like to know
     * @return the enabled actions
     */
    Collection<A> getEnabledActionsFor(S state);

    /**
     * Gets the enabled actions for a given state using the current precision.
     *
     * @param state           the state whose enabled actions we would like to know
     * @param exploredActions the actions already explored from the given state
     * @param prec            the current precision
     * @return the enabled actions
     */
    default <P extends Prec> Collection<A> getEnabledActionsFor(S state, Collection<A> exploredActions, P prec) {
        return getEnabledActionsFor(state);
    }
}
