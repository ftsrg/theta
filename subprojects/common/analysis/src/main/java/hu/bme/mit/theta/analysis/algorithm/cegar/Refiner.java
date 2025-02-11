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
package hu.bme.mit.theta.analysis.algorithm.cegar;

import hu.bme.mit.theta.analysis.Cex;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.Proof;

/**
 * Common interface for refiners. It takes a witness and a precision, checks if the counterexample
 * in the witness is feasible and if not, it refines the precision
 */
public interface Refiner<P extends Prec, Pr extends Proof, C extends Cex> {

    /** Checks if the counterexample in the witness is feasible. If not, refines the precision */
    RefinerResult<P, C> refine(Pr witness, P prec);
}
