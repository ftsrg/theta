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
package hu.bme.mit.theta.solver;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.Test;

public class SolverScopeTest {

    private static final class ClosableStub extends SolverStub {
        boolean closed = false;

        @Override
        public void close() {
            closed = true;
        }
    }

    /** A manager that keeps the solvers it creates unless a solver scope adopts them. */
    private static final class TrackingManager extends SolverManager {
        final List<SolverBase> tracked = new ArrayList<>();

        @Override
        public boolean managesSolver(final String name) {
            return true;
        }

        @Override
        public SolverFactory getSolverFactory(final String name) {
            throw new UnsupportedOperationException();
        }

        ClosableStub create() {
            final var solver = new ClosableStub();
            if (!adoptIntoSolverScope(solver)) {
                tracked.add(solver);
            }
            return solver;
        }

        @Override
        public void close() {}
    }

    @Test
    public void solversCreatedInAScopeAreOwnedAndClosedByIt() throws Exception {
        final var manager = new TrackingManager();

        final ClosableStub inScope = SolverManager.withSolverScope(manager::create);
        final ClosableStub outside = manager.create();

        assertTrue(inScope.closed);
        assertFalse(outside.closed);
        assertEquals(List.of(outside), manager.tracked);
    }

    @Test
    public void scopesNestAndCloseOnFailureToo() throws Exception {
        final var manager = new TrackingManager();
        final List<ClosableStub> created = new ArrayList<>();

        try {
            SolverManager.withSolverScope(
                    () -> {
                        created.add(manager.create());
                        SolverManager.withSolverScope(() -> created.add(manager.create()));
                        assertTrue(created.get(1).closed, "inner scope closes its own solver");
                        assertFalse(created.get(0).closed, "outer solver is still in use");
                        throw new IllegalStateException("analysis failed");
                    });
        } catch (IllegalStateException expected) {
            // the scope must still close what it owns
        }

        assertTrue(created.get(0).closed);
        assertTrue(manager.tracked.isEmpty());
    }
}
