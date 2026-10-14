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
package hu.bme.mit.theta.vmt.analysis.mdd;

import hu.bme.mit.theta.analysis.Cex;
import java.util.List;
import java.util.Map;

/**
 * A counterexample of a VMT model: concrete state-variable values per step, and for each step the
 * index of the transition-relation disjunct that was taken ({@code VmtModel.getTransSplit()}), or
 * -1 if it could not be identified. A variable missing from a state can take any value.
 */
public record VmtTrace(List<Map<String, Object>> states, List<Integer> transitions) implements Cex {

    public VmtTrace {
        states = List.copyOf(states);
        transitions = List.copyOf(transitions);
    }

    @Override
    public int length() {
        return transitions.size();
    }
}
