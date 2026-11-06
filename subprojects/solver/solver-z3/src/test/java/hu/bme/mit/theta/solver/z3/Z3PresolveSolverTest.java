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
package hu.bme.mit.theta.solver.z3;

import hu.bme.mit.theta.solver.SolverFactory;

/** Runs the shared solver tests on the presolving solver, too. */
public final class Z3PresolveSolverTest {

    private Z3PresolveSolverTest() {}

    static final class Core extends Z3SolverTest {
        @Override
        protected SolverFactory solverFactory() {
            return Z3SolverFactory.getPresolveInstance();
        }
    }

    static final class Interpolation extends Z3ItpSolverTest {
        @Override
        protected SolverFactory solverFactory() {
            return Z3SolverFactory.getPresolveInstance();
        }
    }

    static final class Bitvector extends Z3SolverBVTest {
        @Override
        protected SolverFactory solverFactory() {
            return Z3SolverFactory.getPresolveInstance();
        }
    }

    static final class FloatingPoint extends Z3SolverFPTest {
        @Override
        protected SolverFactory solverFactory() {
            return Z3SolverFactory.getPresolveInstance();
        }
    }

    static final class Utils extends SolverUtilsTest {
        @Override
        protected SolverFactory solverFactory() {
            return Z3SolverFactory.getPresolveInstance();
        }
    }
}
