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

package hu.bme.mit.theta.solver.validator;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;

public final class SolverValidatorWrapperFactory implements SolverFactory {

    private final String solverName;

    private SolverValidatorWrapperFactory(String solverName) {
        this.solverName = solverName;
    }

    public static SolverValidatorWrapperFactory create(String solverName) {
        return new SolverValidatorWrapperFactory(solverName);
    }

    @Override
    public Solver createSolver() {
        try {
            return new SolverValidatorWrapper(solverName);

        } catch (Exception e) {
            e.printStackTrace();
            throw new UnsupportedOperationException("Verifying solver could not be created");
        }
    }

    @Override
    public UCSolver createUCSolver() {
        try {
            return new UCSolverValidatorWrapper(solverName);
        } catch (Exception e) {
            e.printStackTrace();
            throw new UnsupportedOperationException("Verifying UCSolver could not be created");
        }
    }

    @Override
    public ItpSolver createItpSolver() {
        try {
            return new ItpSolverValidatorWrapper(solverName);
        } catch (Exception e) {
            e.printStackTrace();
            throw new UnsupportedOperationException("Verifying ITPSolver could not be created");
        }
    }
}
