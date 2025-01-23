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
package hu.bme.mit.theta.solver.smtlib.impl.princess;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.*;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibEnumStrategy;
import java.nio.file.Path;
import java.util.EnumSet;

public class PrincessSmtLibSolverFactory extends GenericSmtLibSolverFactory {

    private PrincessSmtLibSolverFactory(
            Path solverPath, String[] args, final SmtLibEnumStrategy enumStrategy) {
        super(
                solverPath,
                args,
                EnumSet.of(GenericSmtLibSolverBinary.Solver.PRINCESS),
                enumStrategy);
    }

    public static PrincessSmtLibSolverFactory create(
            Path solverPath, String[] args, final SmtLibEnumStrategy enumStrategy) {
        return new PrincessSmtLibSolverFactory(solverPath, args, enumStrategy);
    }

    @Override
    public ItpSolver createItpSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable, enumStrategy);
        final var solverBinary =
                new GenericSmtLibSolverBinary(
                        solverPath, args, EnumSet.of(GenericSmtLibSolverBinary.Solver.PRINCESS));

        return new PrincessSmtLibItpSolver(
                symbolTable, transformationManager, termTransformer, solverBinary, enumStrategy);
    }
}
