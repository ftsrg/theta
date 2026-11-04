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

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.solver.HornSolver;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;
import java.util.Map;
import org.jetbrains.annotations.NotNull;

public final class Z3SolverFactory implements SolverFactory {

    private static final Z3SolverFactory INSTANCE;
    private static final Z3SolverFactory PRESOLVE_INSTANCE;

    static {
        loadLibraries();
        INSTANCE = new Z3SolverFactory(false);
        PRESOLVE_INSTANCE = new Z3SolverFactory(true);
    }

    private final boolean presolve;

    private Z3SolverFactory(final boolean presolve) {
        this.presolve = presolve;
    }

    public static Z3SolverFactory getInstance() {
        return INSTANCE;
    }

    /**
     * Solvers of this factory eliminate defined variables before each check, and restart each check
     * from scratch. This suits queries with long chains of nested array stores.
     */
    public static Z3SolverFactory getPresolveInstance() {
        return PRESOLVE_INSTANCE;
    }

    private static void loadLibraries() {
        switch (OsHelper.getOs()) {
            case WINDOWS:
                System.loadLibrary("libz3java");
                break;
            case LINUX:
            case MAC:
                System.loadLibrary("z3java");
                break;
            default:
                throw new UnsupportedOperationException("Operating system not supported.");
        }
    }

    @Override
    public Solver createSolver() {
        return createSolverInternal();
    }

    @Override
    public UCSolver createUCSolver() {
        return createSolverInternal();
    }

    @Override
    public ItpSolver createItpSolver() {
        return createSolverInternal();
    }

    @NotNull private Z3Solver createSolverInternal() {
        final com.microsoft.z3.Context z3Context = new com.microsoft.z3.Context();
        final com.microsoft.z3.Solver z3Solver =
                presolve
                        ? z3Context.mkSolver(
                                z3Context.andThen(
                                        z3Context.mkTactic("simplify"),
                                        z3Context.mkTactic("propagate-values"),
                                        z3Context.mkTactic("solve-eqs"),
                                        z3Context.mkTactic("smt")))
                        : z3Context.mkSimpleSolver();

        final Z3SymbolTable symbolTable = new Z3SymbolTable();
        final Z3TransformationManager transformationManager =
                new Z3TransformationManager(symbolTable, z3Context);
        final Z3TermTransformer termTransformer = new Z3TermTransformer(symbolTable);

        return new Z3Solver(
                symbolTable, transformationManager, termTransformer, z3Context, z3Solver);
    }

    public HornSolver createHornSolver() {
        final com.microsoft.z3.Context z3Context =
                new com.microsoft.z3.Context(Map.of("proof", "true"));
        final com.microsoft.z3.Solver z3Solver = z3Context.mkSolver("HORN");

        final Z3SymbolTable symbolTable = new Z3SymbolTable();
        final Z3TransformationManager transformationManager =
                new Z3TransformationManager(symbolTable, z3Context);
        final Z3TermTransformer termTransformer = new Z3TermTransformer(symbolTable);

        return new Z3HornSolver(
                symbolTable, transformationManager, termTransformer, z3Context, z3Solver);
    }
}
