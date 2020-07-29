package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.*;

import static hu.bme.mit.theta.core.utils.BvUtils.sint16ToBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.uint16ToBvLitExpr;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.*;
import static org.junit.Assert.*;
import static org.junit.runners.Parameterized.*;

@RunWith(Parameterized.class)
public class BvBasicOperationTest {
    private final Class<?> bvExpr;
    private final Expr<BvType> lhs;
    private final Expr<BvType> rhs;

    @Parameters
    public static Collection<?> operations() {
        return Arrays.asList(new Object[][] {
            /* Unsigned basic operations */
            { BvAddExpr.class, UBv16(4), Add(List.of(UBv16(1), UBv16(3))) },
            { BvSubExpr.class, UBv16(1), Sub(UBv16(4), UBv16(3)) },
            { BvMulExpr.class, UBv16(12), Mul(List.of(UBv16(4), UBv16(3))) },
            { BvDivExpr.class, UBv16(4), Div(UBv16(12), UBv16(3)) },
            { BvModExpr.class, UBv16(1), Mod(UBv16(13), UBv16(3)) },
            { BvRemExpr.class, UBv16(1), Rem(UBv16(13), UBv16(3)) },
                
            /* Signed basic operations (positive) */
            { BvAddExpr.class, SBv16(4), Add(List.of(SBv16(1), SBv16(3))) },
            { BvSubExpr.class, SBv16(1), Sub(SBv16(4), SBv16(3)) },
            { BvMulExpr.class, SBv16(12), Mul(List.of(SBv16(4), SBv16(3))) },
            { BvDivExpr.class, SBv16(4), Div(SBv16(12), SBv16(3)) },
            { BvModExpr.class, SBv16(1), Mod(SBv16(13), SBv16(3)) },
            { BvRemExpr.class, SBv16(1), Rem(SBv16(13), SBv16(3)) },

            /* Signed basic operations (negative) */
            { BvAddExpr.class, SBv16(4), Add(List.of(SBv16(-1), SBv16(5))) },
            { BvSubExpr.class, SBv16(-2), Sub(SBv16(4), SBv16(6)) },
            { BvMulExpr.class, SBv16(-12), Mul(List.of(SBv16(-4), SBv16(3))) },
            { BvDivExpr.class, SBv16(-4), Div(SBv16(12), SBv16(-3)) },
            { BvModExpr.class, SBv16(2), Mod(SBv16(-13), SBv16(3)) },
            { BvRemExpr.class, SBv16(-1), Rem(SBv16(13), SBv16(-3)) },
            { BvNegExpr.class, SBv16(-13), Neg(SBv16(13)) },

            /* Signed basic operations (overflow) */
            { BvAddExpr.class, SBv16(-32768), Add(List.of(SBv16(32767), SBv16(1))) },
            { BvSubExpr.class, SBv16(32767), Sub(SBv16(-32768), SBv16(1)) },
            { BvMulExpr.class, SBv16(-32768), Mul(List.of(SBv16(16384), SBv16(2))) },
        });
    }

    public BvBasicOperationTest(Class<?> bvExpr, Expr<BvType> lhs, Expr<BvType> rhs) {
        this.bvExpr = bvExpr;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    @Test
    public void testOperationEquals() {
        Valuation val = ImmutableValuation.builder().build();
        assertNotNull(bvExpr);
        assertEquals(lhs.eval(val), rhs.eval(val));
    }

    @Test
    public void testOperationNotEquals() {
        Valuation val = ImmutableValuation.builder().build();
        assertNotNull(bvExpr);
        assertNotEquals((rhs.getType().isSigned() ? SBv16(0) : UBv16(0)).eval(val), rhs.eval(val));
    }

    private static BvLitExpr UBv16(int integer) {
        return uint16ToBvLitExpr(integer);
    }

    private static BvLitExpr SBv16(int integer) {
        return sint16ToBvLitExpr(integer);
    }
}
