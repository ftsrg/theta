package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.bvtype.*;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.*;
import static hu.bme.mit.theta.core.utils.BvUtils.sint16ToBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.uint16ToBvLitExpr;

public class BvTestUtils {
    public static Collection<?> BasicOperations() {
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
            { BvRemExpr.class, SBv16(1), Rem(SBv16(13), SBv16(3)) },
            { BvRemExpr.class, SBv16(1), Rem(SBv16(13), SBv16(-3)) },
            { BvRemExpr.class, SBv16(-1), Rem(SBv16(-13), SBv16(3)) },
            { BvRemExpr.class, SBv16(-1), Rem(SBv16(-13), SBv16(-3)) },
            { BvNegExpr.class, SBv16(-13), Neg(SBv16(13)) },

            /* Signed basic operations (overflow) */
            { BvAddExpr.class, SBv16(-32768), Add(List.of(SBv16(32767), SBv16(1))) },
            { BvSubExpr.class, SBv16(32767), Sub(SBv16(-32768), SBv16(1)) },
            { BvMulExpr.class, SBv16(-32768), Mul(List.of(SBv16(16384), SBv16(2))) },
        });
    }

    public static Collection<?> BitvectorOperations() {
        return Arrays.asList(new Object[][] {
            /* Unsigned bitvector specific operations */
            { BvAndExpr.class, UBv16(1), And(List.of(UBv16(7), UBv16(9))) },
            { BvXorExpr.class, UBv16(14), Xor(List.of(UBv16(7), UBv16(9))) },
            { BvOrExpr.class, UBv16(15), Or(List.of(UBv16(7), UBv16(9))) },
            { BvShiftLeftExpr.class, UBv16(56), ShiftLeft(UBv16(7), UBv16(3)) },
            { BvArithShiftRightExpr.class, UBv16(3), ArithShiftRight(UBv16(7), UBv16(1)) },
            { BvLogicShiftRightExpr.class, UBv16(3), LogicShiftRight(UBv16(7), UBv16(1)) },
            { BvRotateLeftExpr.class, UBv16(13), RotateLeft(UBv16(16387), UBv16(2)) },
            { BvRotateRightExpr.class, UBv16(16387), RotateRight(UBv16(13), UBv16(2)) },

            /* Signed bitvector specific operations (positive) */
            { BvAndExpr.class, SBv16(1), And(List.of(SBv16(7), SBv16(9))) },
            { BvXorExpr.class, SBv16(14), Xor(List.of(SBv16(7), SBv16(9))) },
            { BvOrExpr.class, SBv16(15), Or(List.of(SBv16(7), SBv16(9))) },
            { BvShiftLeftExpr.class, SBv16(56), ShiftLeft(SBv16(7), SBv16(3)) },
            { BvArithShiftRightExpr.class, SBv16(3), ArithShiftRight(SBv16(7), SBv16(1)) },
            { BvLogicShiftRightExpr.class, SBv16(3), LogicShiftRight(SBv16(7), SBv16(1)) },
            { BvRotateLeftExpr.class, SBv16(13), RotateLeft(SBv16(16387), SBv16(2)) },
            { BvRotateRightExpr.class, SBv16(16387), RotateRight(SBv16(13), SBv16(2)) },

            /* Signed bitvector specific operations (negative) */
            { BvAndExpr.class, SBv16(9), And(List.of(SBv16(-7), SBv16(9))) },
            { BvXorExpr.class, SBv16(-16), Xor(List.of(SBv16(-7), SBv16(9))) },
            { BvOrExpr.class, SBv16(-7), Or(List.of(SBv16(-7), SBv16(9))) },
            { BvShiftLeftExpr.class, SBv16(-28), ShiftLeft(SBv16(-7), SBv16(2)) },
            { BvArithShiftRightExpr.class, SBv16(-2), ArithShiftRight(SBv16(-7), SBv16(2)) },
            { BvLogicShiftRightExpr.class, SBv16(16382), LogicShiftRight(SBv16(-7), SBv16(2)) },
            { BvRotateLeftExpr.class, SBv16(14), RotateLeft(SBv16(-32765), SBv16(2)) },
            { BvRotateRightExpr.class, SBv16(-32765), RotateRight(SBv16(14), SBv16(2)) },
            { BvNotExpr.class, SBv16(-8), Not(SBv16(7)) },
        });
    }
    
    public static Collection<?> RelationalOperations() {
        return Arrays.asList(new Object[][] {
            /* Unsigned relational operations */
            { BvEqExpr.class, True(), Eq(UBv16(4), UBv16(4)) },
            { BvEqExpr.class, False(), Eq(UBv16(4), UBv16(5)) },
            { BvNeqExpr.class, False(), Neq(UBv16(4), UBv16(4)) },
            { BvNeqExpr.class, True(), Neq(UBv16(4), UBv16(5)) },
            { BvLtExpr.class, True(), Lt(UBv16(4), UBv16(5)) },
            { BvLtExpr.class, False(), Lt(UBv16(4), UBv16(4)) },
            { BvLtExpr.class, False(), Lt(UBv16(4), UBv16(3)) },
            { BvLeqExpr.class, True(), Leq(UBv16(4), UBv16(5)) },
            { BvLeqExpr.class, True(), Leq(UBv16(4), UBv16(4)) },
            { BvLeqExpr.class, False(), Leq(UBv16(4), UBv16(3)) },
            { BvGtExpr.class, False(), Gt(UBv16(4), UBv16(5)) },
            { BvGtExpr.class, False(), Gt(UBv16(4), UBv16(4)) },
            { BvGtExpr.class, True(), Gt(UBv16(4), UBv16(3)) },
            { BvGeqExpr.class, False(), Geq(UBv16(4), UBv16(5)) },
            { BvGeqExpr.class, True(), Geq(UBv16(4), UBv16(4)) },
            { BvGeqExpr.class, True(), Geq(UBv16(4), UBv16(3)) },

            /* Signed relational operations */
            { BvEqExpr.class, True(), Eq(SBv16(4), SBv16(4)) },
            { BvEqExpr.class, False(), Eq(SBv16(4), SBv16(5)) },
            { BvNeqExpr.class, False(), Neq(SBv16(4), SBv16(4)) },
            { BvNeqExpr.class, True(), Neq(SBv16(4), SBv16(5)) },
            { BvLtExpr.class, True(), Lt(SBv16(4), SBv16(5)) },
            { BvLtExpr.class, False(), Lt(SBv16(4), SBv16(4)) },
            { BvLtExpr.class, False(), Lt(SBv16(4), SBv16(3)) },
            { BvLeqExpr.class, True(), Leq(SBv16(4), SBv16(5)) },
            { BvLeqExpr.class, True(), Leq(SBv16(4), SBv16(4)) },
            { BvLeqExpr.class, False(), Leq(SBv16(4), SBv16(3)) },
            { BvGtExpr.class, False(), Gt(SBv16(4), SBv16(5)) },
            { BvGtExpr.class, False(), Gt(SBv16(4), SBv16(4)) },
            { BvGtExpr.class, True(), Gt(SBv16(4), SBv16(3)) },
            { BvGeqExpr.class, False(), Geq(SBv16(4), SBv16(5)) },
            { BvGeqExpr.class, True(), Geq(SBv16(4), SBv16(4)) },
            { BvGeqExpr.class, True(), Geq(SBv16(4), SBv16(3)) },
        });
    }

    private static BvLitExpr UBv16(int integer) {
        return uint16ToBvLitExpr(integer);
    }

    private static BvLitExpr SBv16(int integer) {
        return sint16ToBvLitExpr(integer);
    }
}
