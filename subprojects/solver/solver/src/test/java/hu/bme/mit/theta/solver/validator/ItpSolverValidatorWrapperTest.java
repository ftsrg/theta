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
package hu.bme.mit.theta.solver.validator;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.Interpolant;
import hu.bme.mit.theta.solver.ItpMarker;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import hu.bme.mit.theta.solver.ItpPattern;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.impl.StackImpl;
import java.util.Collection;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

/**
 * The interpolants of a stubbed backend, checked against a brute-force solver over one variable
 * {@code x}: the A side asserts {@code x}, the B side {@code !x}.
 */
public class ItpSolverValidatorWrapperTest {

    private static final String NAME = "itp-validator-wrapper-test-stub";
    private static final ConstDecl<BoolType> X = Const("x", Bool());

    private static SolverFactory inner;

    @BeforeAll
    public static void registerStub() {
        SolverManager.registerSolverManager(
                new SolverManager() {
                    @Override
                    public boolean managesSolver(final String name) {
                        return NAME.equals(name);
                    }

                    @Override
                    public SolverFactory getSolverFactory(final String name) {
                        return inner;
                    }

                    @Override
                    public void close() {}
                });
    }

    @AfterAll
    public static void unregisterStub() throws Exception {
        SolverManager.closeAll();
    }

    private final ItpMarker a = new ItpMarker() {};
    private final ItpMarker b = new ItpMarker() {};
    private final ItpPattern pattern =
            (ItpPattern.Tree<ItpMarker>) () -> ItpMarkerTree.Tree(b, ItpMarkerTree.Leaf(a));

    /** A wrapped solver whose backend answers {@code itpOfA} for the A side. */
    private ItpSolver answering(final Expr<BoolType> itpOfA) {
        final ItpSolver backend = mock(ItpSolver.class);
        final Interpolant interpolant = marker -> marker == a ? itpOfA : False();
        when(backend.getInterpolant(any())).thenReturn(interpolant);
        inner = mock(SolverFactory.class);
        when(inner.createItpSolver()).thenReturn(backend);
        when(inner.createSolver()).thenAnswer(invocation -> new BruteForceSolver());
        return SolverValidatorWrapperFactory.create(NAME).createItpSolver();
    }

    @Test
    public void aValidInterpolantPasses() {
        final ItpSolver solver = answering(X.getRef());
        solver.add(a, X.getRef());
        solver.add(b, Not(X.getRef()));
        assertDoesNotThrow(() -> solver.getInterpolant(pattern));
    }

    @Test
    public void anInterpolantNotImpliedByItsSideFails() {
        final ItpSolver solver = answering(False());
        solver.add(a, X.getRef());
        solver.add(b, Not(X.getRef()));
        final var e = assertThrows(RuntimeException.class, () -> solver.getInterpolant(pattern));
        assertTrue(e.getMessage().contains("not implied"), e.getMessage());
    }

    @Test
    public void anInterpolantConsistentWithTheOtherSideFails() {
        final ItpSolver solver = answering(True());
        solver.add(a, X.getRef());
        solver.add(b, Not(X.getRef()));
        final var e = assertThrows(RuntimeException.class, () -> solver.getInterpolant(pattern));
        assertTrue(e.getMessage().contains("not refuting"), e.getMessage());
    }

    @Test
    public void poppedAssertionsDoNotCount() {
        // `True` would refute a B side that still held the popped `False`
        final ItpSolver solver = answering(True());
        solver.add(a, X.getRef());
        solver.push();
        solver.push();
        solver.add(b, False());
        solver.pop(2);
        solver.add(b, Not(X.getRef()));
        assertThrows(RuntimeException.class, () -> solver.getInterpolant(pattern));
    }

    /** Decides satisfiability by trying both values of {@link #X}. */
    private static final class BruteForceSolver implements Solver {
        private final Stack<Expr<BoolType>> assertions = new StackImpl<>();
        private SolverStatus status;

        @Override
        public void add(final Expr<BoolType> assertion) {
            assertions.add(assertion);
        }

        @Override
        public SolverStatus check() {
            status = SolverStatus.UNSAT;
            for (final boolean value : new boolean[] {false, true}) {
                final Valuation valuation =
                        ImmutableValuation.builder().put(X, Bool(value)).build();
                if (assertions.toCollection().stream()
                        .allMatch(e -> e.eval(valuation).equals(True()))) {
                    status = SolverStatus.SAT;
                }
            }
            return status;
        }

        @Override
        public void push() {
            assertions.push();
        }

        @Override
        public void pop(final int n) {
            assertions.pop(n);
        }

        @Override
        public void reset() {
            assertions.clear();
        }

        @Override
        public SolverStatus getStatus() {
            return status;
        }

        @Override
        public Valuation getModel() {
            throw new UnsupportedOperationException();
        }

        @Override
        public Collection<Expr<BoolType>> getAssertions() {
            return assertions.toCollection();
        }

        @Override
        public void close() {}
    }
}
