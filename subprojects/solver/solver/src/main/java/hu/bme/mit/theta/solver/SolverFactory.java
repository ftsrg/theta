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
package hu.bme.mit.theta.solver;

/**
 * Interface for solver factories that can instantiate solvers. Stores a configuration of a solver,
 * and creates instances with that configuration.
 */
public interface SolverFactory {

    /**
     * Create a basic solver instance.
     *
     * @return Solver instance
     */
    Solver createSolver();

    /**
     * Create a solver that is capable of producing unsat cores.
     *
     * @return Solver instance
     */
    UCSolver createUCSolver();

    /**
     * Create a solver that is capable of interpolation.
     *
     * @return Solver instance
     */
    ItpSolver createItpSolver();

    /**
     * Create a solver that is capable of horn solving (CHC).
     *
     * @return Solver instance
     */
    default HornSolver createHornSolver() {
        throw new UnsupportedOperationException();
    }

}
