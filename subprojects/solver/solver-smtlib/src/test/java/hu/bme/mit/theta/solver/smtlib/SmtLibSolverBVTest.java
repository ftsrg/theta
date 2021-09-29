package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.utils.BvTestUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import org.junit.AfterClass;
import org.junit.Assume;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class SmtLibSolverBVTest {
    private static final String SOLVER = "z3";
    private static final String VERSION = "4.5.0";
    private static boolean solverInstalled = false;
    private static SmtLibSolverManager solverManager;

    @Parameterized.Parameter(0)
    public Class<?> exprType;

    @Parameterized.Parameter(1)
    public Expr<?> expected;

    @Parameterized.Parameter(2)
    public Expr<?> actual;

    @BeforeClass
    public static void init() throws SmtLibSolverInstallerException, IOException {
        if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
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
        if(solverInstalled) solverManager.uninstall(SOLVER, VERSION);
    }

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
    public void testOperationEquals() throws Exception {
        Assume.assumeTrue(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX));

        // Sanity check
        assertNotNull(exprType);
        assertNotNull(expected);
        assertNotNull(actual);

        // Type checks
        assertTrue(
            "The type of actual is " + actual.getClass().getName() + " instead of " + exprType.getName(),
            exprType.isInstance(actual)
        );
        assertEquals(
            "The type of expected (" + expected.getType() + ") must match the type of actual (" + actual.getType() + ")",
            expected.getType(),
            actual.getType()
        );

        // Equality check
        try(final Solver solver = solverManager.getSolverFactory(SOLVER, VERSION).createSolver()) {
            solver.push();

            solver.add(EqExpr.create2(expected, actual));

            SolverStatus status = solver.check();
            assertTrue(status.isSat());
        }
    }
}
