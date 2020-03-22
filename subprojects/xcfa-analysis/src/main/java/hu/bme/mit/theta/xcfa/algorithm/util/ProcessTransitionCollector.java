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
package hu.bme.mit.theta.xcfa.algorithm.util;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.XCFA.Process.Procedure;
import hu.bme.mit.theta.xcfa.expl.ProcedureData;
import hu.bme.mit.theta.xcfa.expl.Transition;

import java.util.Collection;
import java.util.HashSet;

// collects all transitions from a given process
public class ProcessTransitionCollector {
    public static Collection<Transition> getAllTransitionsByProcess(XCFA.Process process) {
        Collection<Transition> result = new HashSet<>();
        for (Procedure p: process.getProcedures()) {
            var locations = ProcedureData.getInstance(p, process).listAllLocations();
            for (ProcedureData.LocationWrapper loc : locations) {
                result.addAll(loc.getTransitions());
            }
        }
        return result;
    }
}
