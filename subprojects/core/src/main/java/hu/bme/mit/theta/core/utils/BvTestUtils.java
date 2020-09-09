package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.bvtype.BvAddExpr;
import hu.bme.mit.theta.core.type.bvtype.BvAndExpr;
import hu.bme.mit.theta.core.type.bvtype.BvArithShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvConcatExpr;
import hu.bme.mit.theta.core.type.bvtype.BvEqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvExtractExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLogicShiftRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvMulExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNegExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvNotExpr;
import hu.bme.mit.theta.core.type.bvtype.BvOrExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvRotateRightExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSExtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSLtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSModExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSRemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvShiftLeftExpr;
import hu.bme.mit.theta.core.type.bvtype.BvSubExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUDivExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvUGtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULeqExpr;
import hu.bme.mit.theta.core.type.bvtype.BvULtExpr;
import hu.bme.mit.theta.core.type.bvtype.BvURemExpr;
import hu.bme.mit.theta.core.type.bvtype.BvXorExpr;
import hu.bme.mit.theta.core.type.bvtype.BvZExtExpr;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Add;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.And;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ArithShiftRight;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Concat;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Eq;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Extract;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.LogicShiftRight;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Mul;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Neg;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Neq;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Not;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Or;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.RotateLeft;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.RotateRight;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SDiv;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SExt;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SGeq;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SGt;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SLeq;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SLt;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SMod;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.SRem;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ShiftLeft;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Sub;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.UDiv;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.UGeq;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.UGt;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ULeq;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ULt;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.URem;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Xor;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.ZExt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToSignedBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToUnsignedBvLitExpr;

public class BvTestUtils {

    private BvTestUtils() {}

    public static Collection<?> BasicOperations() {
        return Arrays.asList(new Object[][] {
            /* Unsigned basic operations */
            { BvAddExpr.class, UBv16(4), Add(List.of(UBv16(1), UBv16(3))) },
            { BvSubExpr.class, UBv16(1), Sub(UBv16(4), UBv16(3)) },
            { BvMulExpr.class, UBv16(12), Mul(List.of(UBv16(4), UBv16(3))) },
            { BvUDivExpr.class, UBv16(4), UDiv(UBv16(12), UBv16(3)) },
            { BvURemExpr.class, UBv16(1), URem(UBv16(13), UBv16(3)) },

            /* Signed basic operations (positive) */
            { BvAddExpr.class, SBv16(4), Add(List.of(SBv16(1), SBv16(3))) },
            { BvSubExpr.class, SBv16(1), Sub(SBv16(4), SBv16(3)) },
            { BvMulExpr.class, SBv16(12), Mul(List.of(SBv16(4), SBv16(3))) },
            { BvSDivExpr.class, SBv16(4), SDiv(SBv16(12), SBv16(3)) },
            { BvSModExpr.class, SBv16(1), SMod(SBv16(13), SBv16(3)) },
            { BvSRemExpr.class, SBv16(1), SRem(SBv16(13), SBv16(3)) },

            /* Signed basic operations (negative) */
            { BvAddExpr.class, SBv16(4), Add(List.of(SBv16(-1), SBv16(5))) },
            { BvSubExpr.class, SBv16(-2), Sub(SBv16(4), SBv16(6)) },
            { BvMulExpr.class, SBv16(-12), Mul(List.of(SBv16(-4), SBv16(3))) },
            { BvSDivExpr.class, SBv16(-4), SDiv(SBv16(12), SBv16(-3)) },
            { BvSModExpr.class, SBv16(2), SMod(SBv16(-13), SBv16(3)) },
            { BvSRemExpr.class, SBv16(1), SRem(SBv16(13), SBv16(3)) },
            { BvSRemExpr.class, SBv16(1), SRem(SBv16(13), SBv16(-3)) },
            { BvSRemExpr.class, SBv16(-1), SRem(SBv16(-13), SBv16(3)) },
            { BvSRemExpr.class, SBv16(-1), SRem(SBv16(-13), SBv16(-3)) },
            { BvNegExpr.class, SBv16(-13), Neg(SBv16(13)) },

            /* Signed basic operations (overflow) */
            { BvAddExpr.class, SBv16(-32768), Add(List.of(SBv16(32767), SBv16(1))) },
            { BvSubExpr.class, SBv16(32767), Sub(SBv16(-32768), SBv16(1)) },
            { BvMulExpr.class, SBv16(-32768), Mul(List.of(SBv16(16384), SBv16(2))) },
        });
    }

    public static Collection<?> BitvectorOperations() {
        return Arrays.asList(new Object[][] {
            /* Concat, extract, extend operations */
            {
                BvConcatExpr.class,
                Bv(new boolean[] { true, false, false, true }),
                Concat(List.of(
                    Bv(new boolean[] { true, false }),
                    Bv(new boolean[] { false, true }))
                )
            },
            {
                BvExtractExpr.class,
                Bv(new boolean[] { false, false }),
                Extract(Bv(new boolean[] { true, false, false, true, false }), Int(2), Int(4))
            },
            {
                BvZExtExpr.class,
                Bv(new boolean[] { false, false, true, false }),
                ZExt(Bv(new boolean[] { true, false }), BvType(4))
            },
            {
                BvSExtExpr.class,
                Bv(new boolean[] { true, true, true, false }),
                SExt(Bv(new boolean[] { true, false }), BvType(4))
            },

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
            { BvULtExpr.class, True(), ULt(UBv16(4), UBv16(5)) },
            { BvULtExpr.class, False(), ULt(UBv16(4), UBv16(4)) },
            { BvULtExpr.class, False(), ULt(UBv16(4), UBv16(3)) },
            { BvULeqExpr.class, True(), ULeq(UBv16(4), UBv16(5)) },
            { BvULeqExpr.class, True(), ULeq(UBv16(4), UBv16(4)) },
            { BvULeqExpr.class, False(), ULeq(UBv16(4), UBv16(3)) },
            { BvUGtExpr.class, False(), UGt(UBv16(4), UBv16(5)) },
            { BvUGtExpr.class, False(), UGt(UBv16(4), UBv16(4)) },
            { BvUGtExpr.class, True(), UGt(UBv16(4), UBv16(3)) },
            { BvUGeqExpr.class, False(), UGeq(UBv16(4), UBv16(5)) },
            { BvUGeqExpr.class, True(), UGeq(UBv16(4), UBv16(4)) },
            { BvUGeqExpr.class, True(), UGeq(UBv16(4), UBv16(3)) },

            /* Signed relational operations */
            { BvEqExpr.class, True(), Eq(SBv16(4), SBv16(4)) },
            { BvEqExpr.class, False(), Eq(SBv16(4), SBv16(5)) },
            { BvNeqExpr.class, False(), Neq(SBv16(4), SBv16(4)) },
            { BvNeqExpr.class, True(), Neq(SBv16(4), SBv16(5)) },
            { BvSLtExpr.class, True(), SLt(SBv16(4), SBv16(5)) },
            { BvSLtExpr.class, False(), SLt(SBv16(4), SBv16(4)) },
            { BvSLtExpr.class, False(), SLt(SBv16(4), SBv16(3)) },
            { BvSLeqExpr.class, True(), SLeq(SBv16(4), SBv16(5)) },
            { BvSLeqExpr.class, True(), SLeq(SBv16(4), SBv16(4)) },
            { BvSLeqExpr.class, False(), SLeq(SBv16(4), SBv16(3)) },
            { BvSGtExpr.class, False(), SGt(SBv16(4), SBv16(5)) },
            { BvSGtExpr.class, False(), SGt(SBv16(4), SBv16(4)) },
            { BvSGtExpr.class, True(), SGt(SBv16(4), SBv16(3)) },
            { BvSGeqExpr.class, False(), SGeq(SBv16(4), SBv16(5)) },
            { BvSGeqExpr.class, True(), SGeq(SBv16(4), SBv16(4)) },
            { BvSGeqExpr.class, True(), SGeq(SBv16(4), SBv16(3)) },
        });
    }

    private static BvLitExpr UBv16(int integer) {
        return bigIntegerToUnsignedBvLitExpr(BigInteger.valueOf(integer), 16);
    }

    private static BvLitExpr SBv16(int integer) {
        return bigIntegerToSignedBvLitExpr(BigInteger.valueOf(integer), 16);
    }
}
