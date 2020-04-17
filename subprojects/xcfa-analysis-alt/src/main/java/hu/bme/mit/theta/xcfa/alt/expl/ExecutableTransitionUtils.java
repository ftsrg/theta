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

public final class ExecutableTransitionUtils {

    private static Optional<ExecutableTransition> optExecutableTransition(ExplState state, Transition transition) {
        return ExecutableTransition.from(state, transition);
    }

    public static Stream<ExecutableTransition> streamExecutableTransitions(ExplState state, Stream<Transition> transitionStream) {
        return transitionStream
                .map(
                        transitionEntry-> optExecutableTransition(state, transitionEntry)
                ).filter(Optional::isPresent)
                .map(Optional::get);
    }

    public static Stream<ExecutableTransition> getExecutableTransitions(ExplState state) {
        if (state.getAtomicLock() == null) {
            return streamExecutableTransitions(state, TransitionUtils.getTransitions(state));
        } else {
            return streamExecutableTransitions(state, TransitionUtils.getTransitions(state, state.getAtomicLock()));
        }
    }
}
