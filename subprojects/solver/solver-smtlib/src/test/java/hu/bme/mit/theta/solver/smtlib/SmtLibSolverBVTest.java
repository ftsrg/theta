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
package hu.bme.mit.theta.solver.smtlib;

import static org.junit.jupiter.api.Assertions.*;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.utils.BvTestUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public class SmtLibSolverBVTest {

    private static boolean solverInstalled = false;
    private static SmtLibSolverManager solverManager;
    private static final String SOLVER = "z3";
    private static final String VERSION = "4.11.2";
    public Class<?> exprType;
    public Expr<?> expected;
    public Expr<?> actual;

    @BeforeAll
    public static void init() throws SmtLibSolverInstallerException, IOException {
        if (OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            Path home = SmtLibSolverManager.HOME;

            solverManager = SmtLibSolverManager.create(home, NullLogger.getInstance());
            try {
                solverManager.install(SOLVER, VERSION, VERSION, null, false);
                solverInstalled = true;
            } catch (SmtLibSolverInstallerException e) {
            }
        }
    }

    @AfterAll
    public static void destroy() throws SmtLibSolverInstallerException {
        if (solverInstalled) {
            solverManager.uninstall(SOLVER, VERSION);
        }
    }

    public static Collection<?> operations() {
        return Stream.concat(
                        BvTestUtils.BasicOperations().stream(),
                        Stream.concat(
                                BvTestUtils.BitvectorOperations().stream(),
                                BvTestUtils.RelationalOperations().stream()))
                .collect(Collectors.toUnmodifiableList());
    }

    @MethodSource("operations")
    @ParameterizedTest(name = "expr: {0}, expected: {1}, actual: {2}")
    public void testOperationEquals(Class<?> exprType, Expr<?> expected, Expr<?> actual) throws Exception {
        initSmtLibSolverBVTest(exprType, expected, actual);
        Assumptions.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX));

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
        try (final Solver solver = solverManager.getSolverFactory(SOLVER, VERSION).createSolver()) {
            solver.push();

            solver.add(EqExpr.create2(expected, actual));

            SolverStatus status = solver.check();
            assertTrue(status.isSat());
        }
    }

    public void initSmtLibSolverBVTest(Class<?> exprType, Expr<?> expected, Expr<?> actual) {
        this.exprType = exprType;
        this.expected = expected;
        this.actual = actual;
    }
}
