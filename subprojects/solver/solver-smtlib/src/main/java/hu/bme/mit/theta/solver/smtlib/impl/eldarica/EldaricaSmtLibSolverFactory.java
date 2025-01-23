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
package hu.bme.mit.theta.solver.smtlib.impl.eldarica;

import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericHornSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibOneshotSolverBinary;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverFactory;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager;
import java.nio.file.Path;

public class EldaricaSmtLibSolverFactory extends GenericSmtLibSolverFactory {

    private EldaricaSmtLibSolverFactory(Path solverPath, String[] args) {
        super(solverPath, args);
    }

    public static EldaricaSmtLibSolverFactory create(Path solverPath, String[] args) {
        return new EldaricaSmtLibSolverFactory(solverPath, args);
    }

    @Override
    public Solver createSolver() {
        throw new UnsupportedOperationException(
                "Eldarica factory cannot create conventional solvers");
    }

    @Override
    public UCSolver createUCSolver() {
        throw new UnsupportedOperationException(
                "Eldarica factory cannot create conventional solvers");
    }

    @Override
    public HornSolver createHornSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibOneshotSolverBinary(solverPath, args);

        return new GenericHornSolver(
                symbolTable, transformationManager, termTransformer, solverBinary);
    }

    @Override
    public ItpSolver createItpSolver() {
        throw new UnsupportedOperationException(
                "Eldarica factory cannot create conventional solvers");
    }
}
