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
package hu.bme.mit.theta.xcfa.alt.expl;

import java.util.*;
import java.util.stream.Stream;

/**
 * Functions for handling executable transitions.
 */
public final class ExecutableTransitionUtils {

    /**
     * Filters the transitions so that only enabled transitions are passed.
     * Different type than Transition, so it's harder to activate a disabled edge.
     * This is the function responsible for checking whether an atomic lock is in place, so
     * every transition -> executableTransition translation should use this function.
     * @param state The state the executableTransition
     * @param transitionStream The transitions to process
     * @return returns a stream of enabled transitions
     */
    public static Stream<ExecutableTransition> streamExecutableTransitions(ExplState state, Stream<Transition> transitionStream) {
        var stream = transitionStream;
        if (state.getAtomicLock() != null) {
            stream = stream.filter(t -> t.getProcess() == state.getAtomicLock());
        }
        return stream.map(
                        transitionEntry -> ExecutableTransition.from(state, transitionEntry)
                ).filter(Optional::isPresent)
                .map(Optional::get);
    }

    /**
     * Returns the list of enabled transitions.
     * @param state The state of execution
     * @return The stream of executable transitions.
     */
    public static Stream<ExecutableTransition> getExecutableTransitions(ExplState state) {
        if (state.getAtomicLock() == null) {
            return streamExecutableTransitions(state, TransitionUtils.getTransitions(state));
        } else {
            return streamExecutableTransitions(state, TransitionUtils.getTransitions(state, state.getAtomicLock()));
        }
    }
}
