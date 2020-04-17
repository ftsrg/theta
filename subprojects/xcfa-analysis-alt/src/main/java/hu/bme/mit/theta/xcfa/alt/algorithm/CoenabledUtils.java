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
package hu.bme.mit.theta.xcfa.alt.algorithm;

import hu.bme.mit.theta.xcfa.alt.expl.ProcessTransitions;
import hu.bme.mit.theta.xcfa.alt.expl.Transition;

public class CoenabledUtils {
    /** returns whether there is a possibility
     * that the two transitions are co-enabled */
    public static boolean coenabled(ProcessTransitions pt, Transition tr) {
        // over-approximations
        // TODO what exactly is this when the process contains two transitions?
        return true;
    }
}
