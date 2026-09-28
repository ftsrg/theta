/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

/**
 * A state that wraps another state. In some cases, we are interested in a specific type of state
 * in the state containment hierarchy which can be conveniently retrieved this way (for example,
 * without implementing a separate case in a switch for all potential wrapper states).
 */
public interface WrapperState extends State {

    /**
     * Returns the wrapped state of the state.
     */
    State getWrappedState();
}
