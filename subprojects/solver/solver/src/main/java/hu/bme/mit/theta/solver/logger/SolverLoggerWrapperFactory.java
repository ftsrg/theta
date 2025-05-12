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
package hu.bme.mit.theta.solver.logger;

import hu.bme.mit.theta.solver.*;
import java.util.Set;

public final class SolverLoggerWrapperFactory implements SolverFactory {

    private final String solverName;
    private final TermLogger termLogger;
    private final Set<SolverLoggerWrapper.SaveStrategy> whenToSave;

    public SolverLoggerWrapperFactory(
            String solverName,
            TermLogger termLogger,
            Set<SolverLoggerWrapper.SaveStrategy> whenToSave) {
        this.solverName = solverName;
        this.termLogger = termLogger;
        this.whenToSave = whenToSave;
    }

    @Override
    public Solver createSolver() {
        try {
            return new SolverLoggerWrapper(
                    SolverManager.resolveSolverFactory(solverName).createSolver(),
                    termLogger,
                    whenToSave);

        } catch (Exception e) {
            e.printStackTrace();
            throw new UnsupportedOperationException("Logging solver could not be created");
        }
    }

    @Override
    public UCSolver createUCSolver() {
        try {
            return new SolverLoggerWrapper(
                    SolverManager.resolveSolverFactory(solverName).createUCSolver(),
                    termLogger,
                    whenToSave);

        } catch (Exception e) {
            e.printStackTrace();
            throw new UnsupportedOperationException("Logging solver could not be created");
        }
    }

    @Override
    public ItpSolver createItpSolver() {
        try {
            return new SolverLoggerWrapper(
                    SolverManager.resolveSolverFactory(solverName).createItpSolver(),
                    termLogger,
                    whenToSave);

        } catch (Exception e) {
            e.printStackTrace();
            throw new UnsupportedOperationException("Logging solver could not be created");
        }
    }

    @Override
    public HornSolver createHornSolver() {
        try {
            return new SolverLoggerWrapper(
                    SolverManager.resolveSolverFactory(solverName).createHornSolver(),
                    termLogger,
                    whenToSave);

        } catch (Exception e) {
            e.printStackTrace();
            throw new UnsupportedOperationException("Logging solver could not be created");
        }
    }
}
