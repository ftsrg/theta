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
package hu.bme.mit.theta.solver.smtlib.impl.mathsat;

import hu.bme.mit.theta.solver.smtlib.solver.SmtLibSolver;
import hu.bme.mit.theta.solver.smtlib.solver.binary.SmtLibSolverBinary;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTermTransformer;
import hu.bme.mit.theta.solver.smtlib.solver.transformer.SmtLibTransformationManager;

/**
 * MathSAT speaks SMT-LIB plus a few extensions. Theta already relies on one of them, {@code
 * get-interpolant}; this class enables a second, {@code check-allsat}, which lets boolean predicate
 * abstraction enumerate its models in a single solver call instead of a blocking-clause loop of one
 * call per model.
 */
public final class MathSATSmtLibSolver extends SmtLibSolver {

    public MathSATSmtLibSolver(
            final SmtLibSymbolTable symbolTable,
            final SmtLibTransformationManager transformationManager,
            final SmtLibTermTransformer termTransformer,
            final SmtLibSolverBinary solverBinary,
            final boolean unsatCoreEnabled) {
        super(symbolTable, transformationManager, termTransformer, solverBinary, unsatCoreEnabled);
    }

    @Override
    public boolean supportsAllSat() {
        return true;
    }
}
