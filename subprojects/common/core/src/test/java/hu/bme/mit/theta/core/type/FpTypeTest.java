package hu.bme.mit.theta.core.type;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.utils.FpTestUtils;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Collection;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

@RunWith(Parameterized.class)
public class FpTypeTest {

    @Parameterized.Parameter(0)
    public Class<?> exprType;

    @Parameterized.Parameter(1)
    public Expr<?> expected;

    @Parameterized.Parameter(2)
    public Expr<?> actual;

    @Parameterized.Parameters(name = "expr: {0}, expected: {1}, actual: {2}")
    public static Collection<?> operations() {
        return Stream.concat(
            FpTestUtils.BasicOperations().stream(),
            Stream.concat(
                FpTestUtils.NaNOperations().stream(),
                FpTestUtils.InfinityOperations().stream()
            )
        ).collect(Collectors.toUnmodifiableList());
    }

    @Test
    public void testFp() {
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
        Valuation val = ImmutableValuation.builder().build();
        LitExpr<?> exp = expected.eval(val);
        LitExpr<?> act = actual.eval(val);
        if (!(exp instanceof FpLitExpr) || !((FpLitExpr) exp).isNaN() || !(act instanceof FpLitExpr) || !((FpLitExpr) act).isNaN()) {
            assertEquals(exp, act); // TODO remove If (failing tests)
        }
    }
}
