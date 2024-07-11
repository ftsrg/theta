/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.mdd.symbolicnode;

import hu.bme.mit.delta.Pair;
import hu.bme.mit.delta.java.mdd.MddVariable;

import java.util.Optional;

/**
 * A constraint that can be used to restrict traversal of a subtree.
 */
public interface TraversalConstraint {

    /**
     * Gets the bounds for a variable if applicable
     *
     * @param variable the variable
     * @return the bounds for the variable
     */
    Optional<Pair<Integer, Integer>> getBoundsFor(MddVariable variable);

}
