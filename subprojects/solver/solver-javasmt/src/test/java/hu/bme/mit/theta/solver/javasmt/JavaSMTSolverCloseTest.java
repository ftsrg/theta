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

import static org.junit.jupiter.api.Assertions.assertThrows;

import hu.bme.mit.theta.solver.SolverBase;
import java.util.List;
import org.junit.jupiter.api.Test;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

public final class JavaSMTSolverCloseTest {

    /** A prover owns solver resources of its own, which closing the context does not free. */
    @Test
    public void closingTheSolverClosesItsProver() throws Exception {
        final var factory = JavaSMTSolverFactory.create(Solvers.SMTINTERPOL, new String[] {});
        for (final SolverBase solver : List.of(factory.createSolver(), factory.createUCSolver())) {
            final var prover = ((JavaSMTSolver) solver).getSolver();
            solver.close();
            assertThrows(IllegalStateException.class, prover::push);
        }
    }
}
