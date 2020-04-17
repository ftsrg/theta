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

public final class ExecutableTransitionForMutableExplState extends ExecutableTransition {
    private final MutableExplState state;
    private final int xVersion;
    public ExecutableTransitionForMutableExplState(MutableExplState state, ExecutableTransition transition,
                                                   int paramVersion) {
        super(transition);
        this.state = state;
        this.xVersion = paramVersion;
    }

    public void execute() {
        Preconditions.checkState(xVersion == state.getVersion(),
                "Mutable explicit state was modified before executing an enabled state. " +
                "You can only execute one transition from the enabled set, then query " +
                "the enabled transitions again.");
        executeInternal(state);
        state.changeVersion();
    }
}
