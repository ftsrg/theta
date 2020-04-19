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

import hu.bme.mit.theta.xcfa.XCFA;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Functions for gathering list of transitions from a given process, state, etc.
 * Every function is global as everything is safe to use.
 * Uses Java 8 Streams to optimize based on usage.
 * (I hope filter.filter.map.filter.blah.blah.findAny is optimized, for example)
 */
public final class TransitionUtils {

    public static Collection<ProcessTransitions> getProcessTransitions(ExplState state) {
        return state.getProcessStates().getStates().entrySet().stream()
                .map(
                        process -> new ProcessTransitions(state, process.getKey(),
                                getTransitionsInternal(process.getKey(), process.getValue()).collect(Collectors.toUnmodifiableSet())
                        )
                ).collect(Collectors.toUnmodifiableSet());
    }

    public static Stream<Transition> getTransitions(ExplState state) {
        return state.getProcessStates().getStates().entrySet().stream()
                .flatMap(TransitionUtils::getTransitionsInternal);
    }

    public static Stream<Transition> getTransitions(ExplState readOnlyState, XCFA.Process process) {
        return getTransitionsInternal(process, readOnlyState.getProcess(process));
    }

    private static Stream<Transition> getTransitionsInternal(Map.Entry<XCFA.Process, ProcessState> ps) {
        return getTransitionsInternal(ps.getKey(), ps.getValue());
    }

    private static Stream<Transition> getTransitionsInternal(XCFA.Process process,
                                                             ProcessState processState) {
        return getTransitionsInternal(process, processState.getActiveCallState(),
                processState.isOutmostCall());
    }

    private static Stream<Transition> getTransitionsInternal(
            XCFA.Process process, CallState callState, boolean outmostCall) {
        // for every edge, create an edge transition
        return Stream.concat(
                callState.getLocation().getOutgoingEdges().stream().map( // edge transitions
                        edge->new EdgeTransition(callState.getProcess(), edge)
                ),
                leaveOnFinal(process, callState, outmostCall).stream() // also, on final location, add leave transition
        );
    }

    private static Optional<Transition> leaveOnFinal(XCFA.Process process, CallState callState,
                                                     boolean outmostCall) {
        if (!outmostCall && callState.isFinal())
            return Optional.of(new LeaveTransition(process, callState));
        return Optional.empty();
    }
}
