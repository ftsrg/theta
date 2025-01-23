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
package hu.bme.mit.theta.solver;

import hu.bme.mit.theta.core.Relation;
import hu.bme.mit.theta.core.Rule;
import java.util.Collection;

/** The HornSolver can provide proofs, and accept Relations */
public interface HornSolver extends Solver {

    default void add(Relation relation) {
        add(relation.getRules().stream().map(Rule::toExpr).toList());
    }

    default void add(Collection<? extends Relation> relations) {
        add(relations.stream().flatMap(it -> it.getRules().stream().map(Rule::toExpr)).toList());
    }

    /** Get the proof found in the solver. */
    default ProofNode getProof() {
        throw new UnsupportedOperationException("Cannot get proof.");
    }
}
