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

package hu.bme.mit.theta.solver.smtlib.impl.generic;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;

import java.nio.file.Path;
import java.util.EnumSet;

public class GenericSmtLibSolverFactory implements SolverFactory {

    protected final Path solverPath;
    protected final String[] args;
    private final EnumSet<GenericSmtLibSolverBinary.Solver> solverOverride;

    protected GenericSmtLibSolverFactory(Path solverPath, String[] args) {
        this(solverPath, args, EnumSet.noneOf(GenericSmtLibSolverBinary.Solver.class));
    }

    protected GenericSmtLibSolverFactory(Path solverPath, String[] args,
                                         EnumSet<GenericSmtLibSolverBinary.Solver> solverOverride) {
        this.solverPath = solverPath;
        this.args = args;
        this.solverOverride = solverOverride;
    }

    public static GenericSmtLibSolverFactory create(Path solverPath, String[] args) {
        return new GenericSmtLibSolverFactory(solverPath, args);
    }

    @Override
    public Solver createSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args, solverOverride);

        return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary,
                false);
    }

    @Override
    public UCSolver createUCSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args, solverOverride);

        return new SmtLibSolver(symbolTable, transformationManager, termTransformer, solverBinary,
                true);
    }

    @Override
    public ItpSolver createItpSolver() {
        throw new UnsupportedOperationException(
                "The generic driver does not support interpolation");
    }
}
