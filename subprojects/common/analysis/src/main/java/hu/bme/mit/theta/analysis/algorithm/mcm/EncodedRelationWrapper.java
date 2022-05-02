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

import hu.bme.mit.theta.solver.Solver;

import java.util.LinkedHashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;

public class EncodedRelationWrapper {
    private final Solver solver;
    private final Map<String, EventConstantLookup> eventLookup;

    public EncodedRelationWrapper(final Solver solver) {
        this.solver = solver;
        this.eventLookup = new LinkedHashMap<>();
    }

    public void addEvent(final String name, final EventConstantLookup lookup) {
        checkState(!eventLookup.containsKey(name), "Name " + name + " already exists in the lookup.");
        eventLookup.put(name, lookup);
    }

    public EventConstantLookup getEventLookup(final String name) {
        return eventLookup.get(name);
    }

    public Solver getSolver() {
        return solver;
    }
}
