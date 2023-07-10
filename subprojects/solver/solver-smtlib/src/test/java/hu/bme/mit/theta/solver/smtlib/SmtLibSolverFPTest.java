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
package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLeqExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpTestUtils;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import org.junit.AfterClass;
import org.junit.Assume;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.kframework.mpfr.BigFloat;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Collection;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.fptype.FpExprs.Abs;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.IsNan;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Leq;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sub;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNE;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class SmtLibSolverFPTest {

    private static boolean solverInstalled = false;
    private static SmtLibSolverManager solverManager;

    private static final String SOLVER = "cvc5";
    private static final String VERSION = "1.0.2";

    @Parameterized.Parameter(0)
    public Class<?> exprType;

    @Parameterized.Parameter(1)
    public Expr<?> expected;

    @Parameterized.Parameter(2)
    public Expr<?> actual;

    @BeforeClass
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

    @AfterClass
    public static void destroy() throws SmtLibSolverInstallerException {
        if (solverInstalled) {
            solverManager.uninstall(SOLVER, VERSION);
        }
    }

    @Parameters(name = "expr: {0}, expected: {1}, actual: {2}")
    public static Collection<?> operations() {
        return FpTestUtils.GetOperations().collect(Collectors.toUnmodifiableList());
    }

    @Test
    public void testOperationEquals() throws Exception {
        Assume.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX));

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
        try (final Solver solver = solverManager.getSolverFactory(SOLVER, VERSION).createSolver()) {
            solver.push();

            if (expected instanceof FpLitExpr && actual.getType() instanceof FpType) {
                if (((FpLitExpr) expected).isNaN()) {
                    //noinspection unchecked
                    solver.add(IsNan((Expr<FpType>) actual));
                } else if (((FpLitExpr) expected).isNegativeInfinity()) {
                    solver.add(EqExpr.create2(expected, actual));
                } else if (((FpLitExpr) expected).isPositiveInfinity()) {
                    solver.add(EqExpr.create2(expected, actual));
                } else {
                    //noinspection unchecked
                    FpLeqExpr leq = Leq(Abs(Sub(RNE, (FpLitExpr) expected, (Expr<FpType>) actual)),
                            FpUtils.bigFloatToFpLitExpr(new BigFloat("1e-2",
                                            FpUtils.getMathContext((FpType) actual.getType(), RNE)),
                                    (FpType) actual.getType()));
                    solver.add(leq);
                }
            } else {
                solver.add(EqExpr.create2(expected, actual));
            }

            SolverStatus status = solver.check();
            assertTrue(status.isSat());
        }
    }
}
