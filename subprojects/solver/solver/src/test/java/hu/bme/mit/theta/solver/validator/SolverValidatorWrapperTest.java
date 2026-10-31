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
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.solver.ItpSolver;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverBase;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.UCSolver;
import java.util.List;
import java.util.function.Function;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

public class SolverValidatorWrapperTest {

    private static final String NAME = "validator-wrapper-test-stub";

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

    @ParameterizedTest
    @ValueSource(strings = {"Solver", "UCSolver", "ItpSolver"})
    public void popForwardsTheLevelCount(final String kind) {
        inner = mock(SolverFactory.class);
        when(inner.createSolver()).thenReturn(mock(Solver.class));
        when(inner.createUCSolver()).thenReturn(mock(UCSolver.class));
        when(inner.createItpSolver()).thenReturn(mock(ItpSolver.class));

        final SolverFactory validating = SolverValidatorWrapperFactory.create(NAME);
        final Function<SolverFactory, SolverBase> create =
                switch (kind) {
                    case "Solver" -> SolverFactory::createSolver;
                    case "UCSolver" -> SolverFactory::createUCSolver;
                    default -> SolverFactory::createItpSolver;
                };
        final SolverBase wrapped = create.apply(validating);
        final SolverBase wrappee = create.apply(inner);

        for (int i = 0; i < 3; i++) {
            wrapped.push();
        }
        wrapped.pop(3);

        verify(wrappee).pop(3);
    }

    private static final Expr<BoolType> X = Const("x", Bool()).getRef();

    /**
     * A wrapped solver that answers UNSAT to {@code x}, cross-checked by a reference that answers
     * {@code referenceStatus}.
     */
    private static Solver unsatCrossCheckedBy(final SolverStatus referenceStatus) {
        final Solver backend = mock(Solver.class);
        when(backend.check()).thenReturn(SolverStatus.UNSAT);
        when(backend.getAssertions()).thenReturn(List.of(X));
        final Solver reference = mock(Solver.class);
        when(reference.check()).thenReturn(referenceStatus);
        when(reference.getModel()).thenReturn(ImmutableValuation.empty());
        final SolverFactory backendFactory = mock(SolverFactory.class);
        when(backendFactory.createSolver()).thenReturn(backend);
        final SolverFactory referenceFactory = mock(SolverFactory.class);
        when(referenceFactory.createSolver()).thenReturn(reference);
        final Solver solver =
                SolverValidatorWrapperFactory.create(backendFactory, referenceFactory)
                        .createSolver();
        solver.add(X);
        return solver;
    }

    @Test
    public void anUnsatTheReferenceAgreesWithPasses() {
        assertDoesNotThrow(unsatCrossCheckedBy(SolverStatus.UNSAT)::check);
    }

    @Test
    public void anUnsatTheReferenceRefutesFails() {
        assertThrows(SolverValidationException.class, unsatCrossCheckedBy(SolverStatus.SAT)::check);
    }
}
