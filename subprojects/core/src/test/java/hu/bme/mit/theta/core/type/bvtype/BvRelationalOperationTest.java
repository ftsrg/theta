package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.ImmutableValuation;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.function.BiFunction;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.*;
import static hu.bme.mit.theta.core.utils.BvUtils.sint16ToBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.uint16ToBvLitExpr;
import static org.junit.Assert.*;
import static org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class BvRelationalOperationTest {
    private final Expr<BvType> lhs;
    private final boolean result;

    @Parameters
    public static Collection<?> operations() {
        return Arrays.asList(new Object[][] {
            /* Unsigned relational operations */
            { Eq(UBv16(4), UBv16(4)), true },
            { Eq(UBv16(4), UBv16(5)), false },
            { Neq(UBv16(4), UBv16(4)), false },
            { Neq(UBv16(4), UBv16(5)), true },
            { Lt(UBv16(4), UBv16(5)), true },
            { Lt(UBv16(4), UBv16(4)), false },
            { Lt(UBv16(4), UBv16(3)), false },
            { Leq(UBv16(4), UBv16(5)), true },
            { Leq(UBv16(4), UBv16(4)), true },
            { Leq(UBv16(4), UBv16(3)), false },
            { Gt(UBv16(4), UBv16(5)), false },
            { Gt(UBv16(4), UBv16(4)), false },
            { Gt(UBv16(4), UBv16(3)), true },
            { Geq(UBv16(4), UBv16(5)), false },
            { Geq(UBv16(4), UBv16(4)), true },
            { Geq(UBv16(4), UBv16(3)), true },
                
            /* Signed relational operations */
            { Eq(SBv16(4), SBv16(4)), true },
            { Eq(SBv16(4), SBv16(5)), false },
            { Neq(SBv16(4), SBv16(4)), false },
            { Neq(SBv16(4), SBv16(5)), true },
            { Lt(SBv16(4), SBv16(5)), true },
            { Lt(SBv16(4), SBv16(4)), false },
            { Lt(SBv16(4), SBv16(3)), false },
            { Leq(SBv16(4), SBv16(5)), true },
            { Leq(SBv16(4), SBv16(4)), true },
            { Leq(SBv16(4), SBv16(3)), false },
            { Gt(SBv16(4), SBv16(5)), false },
            { Gt(SBv16(4), SBv16(4)), false },
            { Gt(SBv16(4), SBv16(3)), true },
            { Geq(SBv16(4), SBv16(5)), false },
            { Geq(SBv16(4), SBv16(4)), true },
            { Geq(SBv16(4), SBv16(3)), true },
        });
    }

    public BvRelationalOperationTest(Expr<BvType> lhs, Boolean result) {
        this.lhs = lhs;
        this.result = result;
    }

    @Test
    public void testOperationEquals() {
        Valuation val = ImmutableValuation.builder().build();
        assertEquals(result ? True() : False(), lhs.eval(val));
    }

    private static BvLitExpr UBv16(int integer) {
        return uint16ToBvLitExpr(integer);
    }

    private static BvLitExpr SBv16(int integer) {
        return sint16ToBvLitExpr(integer);
    }
}
