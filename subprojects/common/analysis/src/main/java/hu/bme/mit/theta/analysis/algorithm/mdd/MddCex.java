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
import hu.bme.mit.theta.analysis.Cex;

public class MddCex implements Cex {

    private final MddHandle violatingStates;

    private MddCex(MddHandle violatingStates) {
        this.violatingStates = violatingStates;
    }

    public static MddCex of(MddHandle violatingStates) {
        return new MddCex(violatingStates);
    }

    @Override
    public int length() {
        return -1;
    }

    public Long size() {
        return MddInterpreter.calculateNonzeroCount(violatingStates);
    }

    public MddHandle getMdd() {
        return violatingStates;
    }
}
