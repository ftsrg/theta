/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.z3legacy;

import com.microsoft.z3legacy.InterpolationContext;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.UCSolver;

public final class Z3LegacySolverFactory implements SolverFactory {

    private static final Z3LegacySolverFactory INSTANCE;

    static {
        loadLibraries();
        INSTANCE = new Z3LegacySolverFactory();
    }

    private Z3LegacySolverFactory() {
    }

    public static Z3LegacySolverFactory getInstance() {
        return INSTANCE;
    }

    private static void loadLibraries() {
        switch (OsHelper.getOs()) {
            case WINDOWS:
                System.loadLibrary("libz3javalegacy");
                break;
            case LINUX:
            case MAC:
                System.loadLibrary("z3javalegacy");
                break;
            default:
                throw new UnsupportedOperationException("Operating system not supported.");
        }
    }

    @Override
    public Solver createSolver() {
        final com.microsoft.z3legacy.Context z3Context = new com.microsoft.z3legacy.Context();
        final com.microsoft.z3legacy.Solver z3Solver = z3Context.mkSimpleSolver();

        final Z3SymbolTable symbolTable = new Z3SymbolTable();
        final Z3TransformationManager transformationManager = new Z3TransformationManager(
                symbolTable, z3Context);
        final Z3TermTransformer termTransformer = new Z3TermTransformer(symbolTable);

        return new Z3Solver(symbolTable, transformationManager, termTransformer, z3Context,
                z3Solver);
    }

    @Override
    public UCSolver createUCSolver() {
        final com.microsoft.z3legacy.Context z3Context = new com.microsoft.z3legacy.Context();
        final com.microsoft.z3legacy.Solver z3Solver = z3Context.mkSimpleSolver();

        final Z3SymbolTable symbolTable = new Z3SymbolTable();
        final Z3TransformationManager transformationManager = new Z3TransformationManager(
                symbolTable, z3Context);
        final Z3TermTransformer termTransformer = new Z3TermTransformer(symbolTable);

        return new Z3Solver(symbolTable, transformationManager, termTransformer, z3Context,
                z3Solver);
    }

    @Override
    public ItpSolver createItpSolver() {
        final InterpolationContext z3Context = InterpolationContext.mkContext();
        final com.microsoft.z3legacy.Solver z3Solver = z3Context.mkSimpleSolver();

        final Z3SymbolTable symbolTable = new Z3SymbolTable();
        final Z3TransformationManager transformationManager = new Z3TransformationManager(
                symbolTable, z3Context);
        final Z3TermTransformer termTransformer = new Z3TermTransformer(symbolTable);

        return new Z3ItpSolver(symbolTable, transformationManager, termTransformer, z3Context,
                z3Solver);
    }

}
