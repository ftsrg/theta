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
package hu.bme.mit.theta.analysis.algorithm.mcm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.LTS;
import hu.bme.mit.theta.analysis.State;

import java.util.Collection;
import java.util.Map;

public class MultiprocLTS<S extends State, A extends Action> {
    private final Map<Integer, LTS<S, A>> ltsMap;

    public MultiprocLTS(final Map<Integer, LTS<S, A>> ltsMap) {
        this.ltsMap = ltsMap;
    }

    public Collection<A> getEnabledActionsFor(final int pid, S state) {
        if (ltsMap.containsKey(pid)) return ltsMap.get(pid).getEnabledActionsFor(state);
        else
            throw new RuntimeException("No such process: " + pid + ". Known processes: " + ltsMap.keySet());
    }

}
