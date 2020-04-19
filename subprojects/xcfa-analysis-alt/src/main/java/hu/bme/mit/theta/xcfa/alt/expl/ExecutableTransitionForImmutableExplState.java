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

/**
 * A wrapper of ExecutableTransition for straight-forward usage in ImmutableExplState.
 * The execute() method should be used, which returns a new ImmutableExplState instance
 * with the transition executed.
 */
public final class ExecutableTransitionForImmutableExplState extends ExecutableTransition {
    private final ImmutableExplState immutableExplState;
    ExecutableTransitionForImmutableExplState(ImmutableExplState immutableExplState, ExecutableTransition transition) {
        super(transition);
        this.immutableExplState = immutableExplState;
    }

    /**
     * @return Returns a new ImmutableExplState with the transition executed.
     */
    public final ImmutableExplState execute() {
        return new ImmutableExplState.Builder(immutableExplState).execute(this).build();
    }
}
