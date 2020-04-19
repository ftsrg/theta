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
import java.util.Objects;
import java.util.stream.Stream;

public final class ProcessTransitions {
    private final XCFA.Process process;
    private final Collection<Transition> transitions;
    private final ExplState state;

    public ProcessTransitions(ExplState state, XCFA.Process process, Collection<Transition> transitions) {
        this.process = process;
        this.transitions = transitions;
        this.state = state;
    }

    public Stream<Transition> transitionStream() {
        return transitions.stream();
    }

    public Stream<ExecutableTransition> enabledStream() {
        return ExecutableTransitionUtils.streamExecutableTransitions(state, transitionStream());
    }

    public boolean hasAnyEnabledTransition() {
        return enabledStream().findAny().isPresent();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        ProcessTransitions that = (ProcessTransitions) o;
        return Objects.equals(process, that.process);
    }

    @Override
    public int hashCode() {
        return Objects.hash(process);
    }

    public XCFA.Process getProcess() {
        return process;
    }
}
