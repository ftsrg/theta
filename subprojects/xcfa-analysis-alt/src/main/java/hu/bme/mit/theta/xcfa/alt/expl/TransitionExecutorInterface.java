/*
 *  Copyright 2017 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.alt.expl;

/**
 * Mutates the given state with a transition.
 * Assumes that the transition is enabled and the state that generated the instance
 * is equivalent to the one passed here.
 * Used for co-locating the enabledness test with the state mutation itself in the source code.
 * Should only be called internally.
 */
@FunctionalInterface
public interface TransitionExecutorInterface {
    void executeInternal(ExplStateMutatorInterface state);
}
