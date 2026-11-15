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
package hu.bme.mit.theta.solver.javasmt;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.OsHelper.OperatingSystem;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.InterruptibleSolver;
import hu.bme.mit.theta.solver.Solver;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

public final class JavaSMTInterruptTest {

    public static List<Solvers> solvers() {
        final List<Solvers> solvers = new ArrayList<>(List.of(Solvers.Z3));
        if (OsHelper.getOs().equals(OperatingSystem.LINUX)) solvers.add(Solvers.YICES2);
        return solvers;
    }

    @MethodSource("solvers")
    @ParameterizedTest(name = "solver: {0}")
    public void testInterruptStopsOnlyThatSolver(Solvers solvers) throws Exception {
        final JavaSMTSolverFactory factory = JavaSMTSolverFactory.create(solvers, new String[] {});
        final ConstDecl<IntType> x = Const("x", Int());
        try (Solver interrupted = factory.createSolver();
                Solver other = factory.createSolver()) {
            interrupted.add(Lt(x.getRef(), Int(1)));
            other.add(Lt(x.getRef(), Int(1)));

            ((InterruptibleSolver) interrupted).interrupt();

            assertThrows(RuntimeException.class, interrupted::check);
            assertTrue(other.check().isSat());
        }
    }
}
