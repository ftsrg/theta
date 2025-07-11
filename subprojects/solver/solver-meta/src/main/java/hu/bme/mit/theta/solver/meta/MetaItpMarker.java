/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.solver.meta;

import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpSolver;

import java.util.Map;

public class MetaItpMarker implements ItpMarker {
    private final Map<ItpSolver, ItpMarker> markerMap;

    public MetaItpMarker(Map<ItpSolver, ItpMarker> markerMap) {
        this.markerMap = markerMap;
    }
    public ItpMarker getMarker(ItpSolver solver) {
        return markerMap.get(solver);
    }
}
