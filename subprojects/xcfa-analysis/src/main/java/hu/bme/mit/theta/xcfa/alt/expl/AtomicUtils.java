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
import hu.bme.mit.theta.xcfa.XCFA;

/**
 * Internal utility for executing atomic statements
 */
final class AtomicUtils {
    public static void begin(MutableExplState state, XCFA.Process process) {
        if (state.getAtomicLock() != null) {
            state.setUnsafe("Atomic begin inside atomic transition");
            return;
        }
        state.setAtomicLock(process);
    }

    public static void end(MutableExplState state, XCFA.Process process) {
        if (state.getAtomicLock() == null) {
            state.setUnsafe("Atomic end outside atomic transition");
            return;
        }
        Preconditions.checkState(state.getAtomicLock() == process, "An (atomic end) transition ran from a different process");
        state.setAtomicLock(null);
    }
}
