/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.mcm.mcm;

import hu.bme.mit.theta.solver.Solver;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkState;

public class EncodedRelationWrapper {
    private final Solver solver;
    private final Map<String, EventConstantLookup> eventLookup;
    private final Map<EventConstantLookup, Boolean> encodedStatus;

    public EncodedRelationWrapper(final Solver solver) {
        this.solver = solver;
        this.eventLookup = new LinkedHashMap<>();
        encodedStatus = new LinkedHashMap<>();
    }

    public void addEvent(final String name, final EventConstantLookup lookup) {
        checkState(!eventLookup.containsKey(name), "Name " + name + " already exists in the lookup.");
        eventLookup.put(name, lookup);
        encodedStatus.put(lookup, false);
    }

    public EventConstantLookup get(final String name) {
        return eventLookup.get(name);
    }

    public void setEncoded(final EventConstantLookup eventConstantLookup) {
        encodedStatus.put(eventConstantLookup, true);
    }

    public boolean isEncoded(final EventConstantLookup eventConstantLookup) {
        return encodedStatus.get(eventConstantLookup);
    }

    public Map<String, EventConstantLookup> getNonEncoded() {
        return eventLookup.entrySet().stream().filter(i -> !isEncoded(i.getValue())).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue));
    }

    public Solver getSolver() {
        return solver;
    }
}
