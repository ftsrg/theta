/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;

import java.util.Collection;
import java.util.Map;

/**
 * Provides the enabled actions for each partition (e.g., thread) in the system
 * @param <S>   The state type
 * @param <A>   The action type
 * @param <SID>   The scope ID type
 * @param <PID>   The PID type
 */
public interface MemoryEventProvider<S extends State, A extends Action, SID, PID> {
    Map<SID, Map<PID, Collection<S>>> getInitialStates();
    Map<SID, Map<PID, Collection<MCMAction<A>>>> getEnabledActionsFor(final S state);
}
