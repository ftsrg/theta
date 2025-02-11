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
package hu.bme.mit.theta.analysis.algorithm.mdd;

import hu.bme.mit.delta.java.mdd.MddHandle;
import hu.bme.mit.delta.mdd.MddInterpreter;
import hu.bme.mit.theta.analysis.algorithm.Proof;

public class MddProof implements Proof {

    private final MddHandle stateSpace;

    private MddProof(MddHandle stateSpace) {
        this.stateSpace = stateSpace;
    }

    public static MddProof of(MddHandle stateSpace) {
        return new MddProof(stateSpace);
    }

    public Long size() {
        return MddInterpreter.calculateNonzeroCount(stateSpace);
    }

    public MddHandle getMdd() {
        return stateSpace;
    }
}
