/*
 *  Copyright 2025 Budapest University of Technology and Economics
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

import static org.junit.jupiter.api.Assertions.*;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.utils.RatTestUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import java.util.Collection;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;

public class JavaSMTSolverRatTest {
    public Class<?> exprType;
    public Expr<?> expected;
    public Expr<?> actual;

    public static Collection<?> operations() {
        return RatTestUtils.BasicOperations();
    }

    @MethodSource("operations")
    @ParameterizedTest(name = "expected: {1}, actual: {2}")
    public void testOperationEquals(Class<?> exprType, Expr<?> expected, Expr<?> actual) {
        initJavaSMTSolverRatTest(exprType, expected, actual);
        // Sanity check
        assertNotNull(exprType);
        assertNotNull(expected);
        assertNotNull(actual);

        // Type checks
        assertTrue(
                exprType.isInstance(actual),
                "The type of actual is "
                        + actual.getClass().getName()
                        + " instead of "
                        + exprType.getName());
        assertEquals(
                expected.getType(),
                actual.getType(),
                "The type of expected ("
                        + expected.getType()
                        + ") must match the type of actual ("
                        + actual.getType()
                        + ")");

        // Equality check
        final Solver solver =
                JavaSMTSolverFactory.create(Solvers.Z3, new String[] {}).createSolver();
        solver.push();

        solver.add(EqExpr.create2(expected, actual));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());
    }

    public void initJavaSMTSolverRatTest(Class<?> exprType, Expr<?> expected, Expr<?> actual) {
        this.exprType = exprType;
        this.expected = expected;
        this.actual = actual;
    }
}
