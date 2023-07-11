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

package hu.bme.mit.theta.solver.smtlib.impl.cvc5;

import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.smtlib.impl.generic.*;
import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;

import java.nio.file.Path;
import java.util.EnumSet;

public class CVC5SmtLibSolverFactory extends GenericSmtLibSolverFactory {

    private CVC5SmtLibSolverFactory(Path solverPath, String[] args) {
        super(solverPath, args);
    }

    public static CVC5SmtLibSolverFactory create(Path solverPath, String[] args) {
        return new CVC5SmtLibSolverFactory(solverPath, args);
    }

    @Override
    public ItpSolver createItpSolver() {
        final var symbolTable = new GenericSmtLibSymbolTable();
        final var transformationManager = new GenericSmtLibTransformationManager(symbolTable);
        final var termTransformer = new GenericSmtLibTermTransformer(symbolTable);
        final var solverBinary = new GenericSmtLibSolverBinary(solverPath, args,
                EnumSet.noneOf(GenericSmtLibSolverBinary.Solver.class));

        return new CVC5SmtLibItpSolver(
                symbolTable, transformationManager, termTransformer, solverBinary,
                () -> new GenericSmtLibSolverBinary(solverPath, args,
                        EnumSet.noneOf(GenericSmtLibSolverBinary.Solver.class))
        );
    }
}
