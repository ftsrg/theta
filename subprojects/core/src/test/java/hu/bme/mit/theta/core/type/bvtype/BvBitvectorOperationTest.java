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
public class BvBitvectorOperationTest {
    private final Class<?> bvExpr;
    private final Expr<BvType> lhs;
    private final Expr<BvType> rhs;

    @Parameters
    public static Collection<?> operations() {
        return Arrays.asList(new Object[][] {
            /* Unsigned bitvector specific operations */
            { BvAndExpr.class, UBv16(1), And(List.of(UBv16(7), UBv16(9))) },
            { BvXorExpr.class, UBv16(14), Xor(List.of(UBv16(7), UBv16(9))) },
            { BvOrExpr.class, UBv16(15), Or(List.of(UBv16(7), UBv16(9))) },
            { BvShiftLeftExpr.class, UBv16(56), ShiftLeft(UBv16(7), UBv16(3)) },
            { BvShiftRightExpr.class, UBv16(3), ShiftRight(UBv16(7), UBv16(1)) },
            
            /* Signed bitvector specific operations (positive) */
            { BvAndExpr.class, SBv16(1), And(List.of(SBv16(7), SBv16(9))) },
            { BvXorExpr.class, SBv16(14), Xor(List.of(SBv16(7), SBv16(9))) },
            { BvOrExpr.class, SBv16(15), Or(List.of(SBv16(7), SBv16(9))) },
            { BvShiftLeftExpr.class, SBv16(56), ShiftLeft(SBv16(7), SBv16(3)) },
            { BvShiftRightExpr.class, SBv16(3), ShiftRight(SBv16(7), SBv16(1)) },

            /* Signed bitvector specific operations (negative) */
            { BvAndExpr.class, SBv16(9), And(List.of(SBv16(-7), SBv16(9))) },
            { BvXorExpr.class, SBv16(-16), Xor(List.of(SBv16(-7), SBv16(9))) },
            { BvOrExpr.class, SBv16(-7), Or(List.of(SBv16(-7), SBv16(9))) },
            { BvShiftLeftExpr.class, SBv16(-28), ShiftLeft(SBv16(-7), SBv16(2)) },
            { BvShiftRightExpr.class, SBv16(-2), ShiftRight(SBv16(-7), SBv16(2)) },
            { BvNotExpr.class, SBv16(-8), Not(SBv16(7)) },
        });
    }

    public BvBitvectorOperationTest(Class<?> bvExpr, Expr<BvType> lhs, Expr<BvType> rhs) {
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
