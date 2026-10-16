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
package hu.bme.mit.theta.solver.z3legacy;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Eq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Lt;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIfEnvironmentVariable;

/**
 * Opt-in (`Z3_STRESS=true`; a native crash kills the JVM): whether the legacy Z3 binding survives
 * many threads using their own solvers at once, as in DSS's concurrent executor.
 */
@EnabledIfEnvironmentVariable(named = "Z3_STRESS", matches = "true")
public final class Z3ConcurrencyStressTest {

    private static final int THREADS = intFromEnv("Z3_STRESS_THREADS", 8);
    private static final int ITERATIONS = intFromEnv("Z3_STRESS_ITERATIONS", 2000);

    private static final Object CREATION_LOCK = new Object();

    @Test
    public void testParallelCreationAndSolving() throws Exception {
        runOnParallelThreads(false, true);
    }

    @Test
    public void testSerializedCreationParallelSolving() throws Exception {
        runOnParallelThreads(true, true);
    }

    @Test
    public void testSerializedCreationParallelSatOnly() throws Exception {
        runOnParallelThreads(true, false);
    }

    private static void runOnParallelThreads(boolean serializeCreation, boolean interpolate)
            throws Exception {
        final ExecutorService executor = Executors.newFixedThreadPool(THREADS);
        final CountDownLatch start = new CountDownLatch(1);
        final List<Future<?>> futures = new ArrayList<>();
        for (int t = 0; t < THREADS; t++) {
            final int offset = t;
            futures.add(
                    executor.submit(
                            () -> {
                                start.await();
                                runQueries(offset, serializeCreation, interpolate);
                                return null;
                            }));
        }
        start.countDown();
        for (Future<?> future : futures) {
            future.get(); // rethrows a Java-level failure of any thread
        }
        executor.shutdown();
        assertTrue(executor.awaitTermination(1, TimeUnit.MINUTES));
    }

    private static void runQueries(int offset, boolean serializeCreation, boolean interpolate)
            throws Exception {
        // Same names in every thread on purpose: DSS blocks share the program's variable names.
        final ConstDecl<IntType> x = Const("x", Int());
        final ConstDecl<IntType> y = Const("y", Int());
        final ConstDecl<IntType> z = Const("z", Int());

        final Solver solver;
        final ItpSolver itpSolver;
        if (serializeCreation) {
            synchronized (CREATION_LOCK) {
                solver = Z3LegacySolverFactory.getInstance().createSolver();
                itpSolver = interpolate ? Z3LegacySolverFactory.getInstance().createItpSolver() : null;
            }
        } else {
            solver = Z3LegacySolverFactory.getInstance().createSolver();
            itpSolver = interpolate ? Z3LegacySolverFactory.getInstance().createItpSolver() : null;
        }
        try (solver;
                itpSolver) {
            for (int i = 0; i < ITERATIONS; i++) {
                final int k = offset * ITERATIONS + i;

                // SAT check with a model: x = y + k, y > k.
                solver.push();
                solver.add(Eq(x.getRef(), Add(y.getRef(), Int(k))));
                solver.add(Gt(y.getRef(), Int(k)));
                assertEquals(SolverStatus.SAT, solver.check());
                assertTrue(solver.getModel().eval(x).isPresent());
                solver.pop();

                if (itpSolver == null) continue;

                // UNSAT binary interpolation: A = (x = y + k, y > k), B = (z = x, z < 2k).
                itpSolver.push();
                final ItpMarker a = itpSolver.createMarker();
                final ItpMarker b = itpSolver.createMarker();
                final ItpPattern pattern = itpSolver.createBinPattern(a, b);
                itpSolver.add(a, Eq(x.getRef(), Add(y.getRef(), Int(k))));
                itpSolver.add(a, Gt(y.getRef(), Int(k)));
                itpSolver.add(b, Eq(z.getRef(), x.getRef()));
                itpSolver.add(b, Lt(z.getRef(), Int(2 * k)));
                assertEquals(SolverStatus.UNSAT, itpSolver.check());
                itpSolver.getInterpolant(pattern).eval(a);
                itpSolver.pop();
            }
        }
    }

    private static int intFromEnv(String name, int defaultValue) {
        final String value = System.getenv(name);
        return value == null ? defaultValue : Integer.parseInt(value);
    }
}
