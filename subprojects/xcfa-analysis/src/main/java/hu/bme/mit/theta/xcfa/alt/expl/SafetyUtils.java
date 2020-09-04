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

import com.google.common.base.Preconditions;

/**
 * Functions for querying/determining whether safety properties were satisfied in a specific state.
 */
final class SafetyUtils {

    private SafetyUtils() { }

    public static Safety getSafety(ExplState state) {
        if (!state.getInternalSafety().isSafe()) {
            return state.getInternalSafety();
        }
        Preconditions.checkState(!state.getInternalSafety().isFinished(), "Internal state cannot be in finished state");
        if (!getLocationSafety(state).isSafe()) {
            return getLocationSafety(state);
        }
        if (getLocationSafety(state).isFinished()) {
            return getLocationSafety(state);
        }
        // When checking deadlock safety, it is required that the program is not yet finished!
        return getDeadlockSafety(state);
    }

    public static Safety getDeadlockSafety(ExplState state) {
        if (ExecutableTransitionUtils.getExecutableTransitions(state).findAny().isEmpty()) {
            return Safety.unsafe("Deadlock");
        }
        return Safety.safe();
    }

    public static Safety getLocationSafety(ExplState state) {
        return getSafety(state.getProcessStates());
    }

    private static Safety mergeAllProcessSafety(Safety a, Safety b) {
        // First "merge" in reduce
        if (a == null)
            return b;
        // Something is unsafe -> result is unsafe
        if (!a.isSafe())
            return a;
        if (!b.isSafe())
            return b;
        // If any process is unfinished, then the program is still running
        if (!a.isFinished())
            return a;
        return b;
    }

    private static Safety getSafety(ProcessStates processStates) {
        return processStates.getStates().values().stream().map(SafetyUtils::getSafety).reduce(null, SafetyUtils::mergeAllProcessSafety);
    }

    public static Safety getSafety(ProcessState processState) {
        var safety = getSafety(processState.getActiveCallState());
        if (!safety.isSafe())
            return safety;
        if (processState.isOutmostCall() && safety.isFinished())
            return Safety.finished();
        return Safety.safe();
    }

    private static Safety getSafety(CallState callState) {
        if (callState.isError())
            return Safety.unsafe("Error location reached");
        if (callState.isFinal())
            return Safety.finished();
        return Safety.safe();
    }
}
