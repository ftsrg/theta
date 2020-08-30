package hu.bme.mit.theta.solver.smtlib;

import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.utils.BvTestUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import hu.bme.mit.theta.solver.smtlib.generic.GenericSmtLibSolverFactory;
import hu.bme.mit.theta.solver.smtlib.manager.SmtLibSolverManager;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

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
    @Parameterized.Parameter(0)
    public Class<?> exprType;

    @Parameterized.Parameter(1)
    public Expr<?> expected;

    @Parameterized.Parameter(2)
    public Expr<?> actual;

    private static final SmtLibSolverManager solverManager = SmtLibSolverManager.create(
        Path.of(System.getProperty("user.home")).resolve(".theta"),
        NullLogger.getInstance()
    );

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
    public void testOperationEquals() throws SmtLibSolverInstallerException {
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
        final Solver solver = solverManager.getSolverFactory("generic", "cvc4").createSolver();
        solver.push();

        solver.add(EqExpr.create2(expected, actual));

        SolverStatus status = solver.check();
        assertTrue(status.isSat());
    }
}
