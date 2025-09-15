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
package hu.bme.mit.theta.solver.smtlib.impl.mathsat;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.UCSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverFactory;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;
import java.nio.file.Path;

public class MathSATSmtLibSolverFactory extends GenericSmtLibSolverFactory {

    private final boolean itpSupported;

    private MathSATSmtLibSolverFactory(Path solverPath, String[] args, boolean itpSupported) {
        super(solverPath, args);
        this.itpSupported = itpSupported;
    }

    public static MathSATSmtLibSolverFactory create(
            Path solverPath, String[] args, boolean itpSupported) {
        return new MathSATSmtLibSolverFactory(solverPath, args, itpSupported);
    }

    @Override
    public Solver createSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new MathSATSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable, enumStrategy);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

        return new SmtLibSolver(
                symbolTable, transformationManager, termTransformer, solverBinary, false);
    }

    @Override
    public UCSolver createUCSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new MathSATSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable, enumStrategy);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

        return new SmtLibSolver(
                symbolTable, transformationManager, termTransformer, solverBinary, true);
    }

    @Override
    public ItpSolver createItpSolver() {
        if (itpSupported) {
            final var symbolTable = new GenericSmtLibSymbolTable();
            final var transformationManager = new MathSATSmtLibTransformationManager(symbolTable);
            final var termTransformer = new GenericSmtLibTermTransformer(symbolTable, enumStrategy);
            final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args);

            return new MathSATSmtLibItpSolver(
                    symbolTable, transformationManager, termTransformer, solverBinary);
        } else {
            throw new UnsupportedOperationException("MathSAT interpolation supported above 5.4.0");
        }
    }
}
