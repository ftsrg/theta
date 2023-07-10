/*
 *  Copyright 2023 Budapest University of Technology and Economics
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

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.utils.BvTestUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.*;
import static org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class Z3SolverBVTest {

    @Parameterized.Parameter(0)
    public Class<?> exprType;

    @Parameterized.Parameter(1)
    public Expr<?> expected;

    @Parameterized.Parameter(2)
    public Expr<?> actual;

    @Parameters(name = "expr: {0}, expected: {1}, actual: {2}")
    public static Collection<?> operations() {
        return Stream.concat(
                BvTestUtils.BasicOperations().stream(),
                Stream.concat(
                        BvTestUtils.BitvectorOperations().stream(),
                        BvTestUtils.RelationalOperations().stream()
                )
        ).collect(Collectors.toUnmodifiableList());
    }

    @Test
    public void testOperationEquals() {
        // Sanity check
        assertNotNull(exprType);
        assertNotNull(expected);
        assertNotNull(actual);

        // Type checks
        assertTrue(
                "The type of actual is " + actual.getClass().getName() + " instead of "
                        + exprType.getName(),
                exprType.isInstance(actual)
        );
        assertEquals(
                "The type of expected (" + expected.getType() + ") must match the type of actual ("
                        + actual.getType() + ")",
                expected.getType(),
                actual.getType()
        );

        // Equality check
        final Solver solver = Z3SolverFactory.getInstance().createSolver();
        solver.push();

        solver.add(EqExpr.create2(expected, actual));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());
    }
}
