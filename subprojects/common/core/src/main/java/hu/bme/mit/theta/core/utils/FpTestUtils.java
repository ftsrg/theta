package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.fptype.*;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.*;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNA;
import static hu.bme.mit.theta.core.type.fptype.FpRoundingMode.RNE;

public class FpTestUtils {

    private FpTestUtils() {}

    public static Collection<?> BasicOperations() {
        return Arrays.asList(new Object[][] {
            { FpAddExpr.class, Fp16("5.5"), Add(RNE, List.of(Fp16("2.1"), Fp16("3.4"))) },
            { FpSubExpr.class, Fp16("2.1"), Sub(RNE, Fp16("5.5"), Fp16("3.4")) },
            { FpPosExpr.class, Fp16("2.1"), Pos(Fp16("2.1")) },
            { FpNegExpr.class, Fp16("-2.1"), Neg(Fp16("2.1")) },
            { FpMulExpr.class, Fp16("7.14"), Mul(RNE, List.of(Fp16("2.1"), Fp16("3.4"))) },
            { FpDivExpr.class, Fp16("2.1"), Div(RNE, Fp16("7.14"), Fp16("3.4")) },
            { FpEqExpr.class, Bool(true), Eq(Fp16("7.14"), Fp16("7.14")) },
            { FpEqExpr.class, Bool(false), Eq(Fp16("7.14"), Fp16("7.15"))  },
            { FpNeqExpr.class, Bool(true), Neq(Fp16("-7.14"), Fp16("7.14"))  },
            { FpNeqExpr.class, Bool(false), Neq(Fp16("-7.14"), Fp16("-7.14"))  },
            { FpAbsExpr.class, Fp16("2.1"), Abs(Fp16("2.1")) },
            { FpAbsExpr.class, Fp16("2.1"), Abs(Fp16("-2.1")) },
            { FpGeqExpr.class, Bool(true), Geq(Fp16("7.14"), Fp16("7.15")) },
            { FpGeqExpr.class, Bool(true), Geq(Fp16("7.14"), Fp16("7.14")) },
            { FpGeqExpr.class, Bool(false), Geq(Fp16("-7.14"), Fp16("-7.15")) },
            { FpGtExpr.class, Bool(true), Gt(Fp16("7.14"), Fp16("7.15")) },
            { FpGtExpr.class, Bool(false), Gt(Fp16("7.14"), Fp16("7.14")) },
            { FpGtExpr.class, Bool(false), Gt(Fp16("-7.14"), Fp16("-7.15")) },
            { FpIsNanExpr.class, Bool(true), IsNan(Fp16NaN()) },
            { FpIsNanExpr.class, Bool(false), IsNan(Fp16PInf()) },
            { FpIsNanExpr.class, Bool(false), IsNan(Fp16NInf()) },
            { FpIsNanExpr.class, Bool(false), IsNan(Fp16("0.0")) },
            { FpLeqExpr.class, Bool(false), Leq(Fp16("7.14"), Fp16("7.15")) },
            { FpLeqExpr.class, Bool(true), Leq(Fp16("7.14"), Fp16("7.14")) },
            { FpLeqExpr.class, Bool(true), Leq(Fp16("-7.14"), Fp16("-7.15")) },
            { FpLtExpr.class, Bool(false), Lt(Fp16("7.14"), Fp16("7.15")) },
            { FpLtExpr.class, Bool(false), Lt(Fp16("7.14"), Fp16("7.14")) },
            { FpLtExpr.class, Bool(true), Lt(Fp16("-7.14"), Fp16("-7.15")) },
            { FpMaxExpr.class, Fp16("2.1"), Max(RNE, Fp16("-2.1"), Fp16("2.1")) },
            { FpMaxExpr.class, Fp16("2.1"), Max(RNE, Fp16("1.9"), Fp16("2.1")) },
            { FpMinExpr.class, Fp16("-2.1"), Min(RNE, Fp16("-2.1"), Fp16("2.1")) },
            { FpMinExpr.class, Fp16("1.9"), Min(RNE, Fp16("1.9"), Fp16("2.1")) },
            { FpRemExpr.class, Fp16("0.1"), Rem(RNE, Fp16("4.3"), Fp16("4.3")) },
            { FpRemExpr.class, Fp16("-0.1"), Rem(RNE, Fp16("-4.3"), Fp16("4.3")) },
            { FpRemExpr.class, Fp16("0.1"), Rem(RNE, Fp16("4.3"), Fp16("-4.3")) },
            { FpRemExpr.class, Fp16("-0.1"), Rem(RNE, Fp16("-4.3"), Fp16("-4.3")) },
            { FpRoundToIntegralExpr.class, Fp16("2.0"), RoundToIntegral(RNE, Fp16("1.5")) },
            { FpRoundToIntegralExpr.class, Fp16("2.0"), RoundToIntegral(RNE, Fp16("2.49")) },
            { FpRoundToIntegralExpr.class, Fp16("-10.0"), RoundToIntegral(RNE, Fp16("-10.49")) },
            { FpSqrtExpr.class, Fp16("2.1"), Sqrt(RNE, Fp16("4.41")) },
            { FpSqrtExpr.class, Fp16("3.0"), Sqrt(RNE, Fp16("9.0")) },
            { FpSqrtExpr.class, Fp16("0.1"), Sqrt(RNE, Fp16("0.01")) },
        });
    }

    public static Collection<?> NaNOperations() {
        return Arrays.asList(new Object[][] {
            { FpAddExpr.class, Fp16NaN(), Add(RNE, List.of(Fp16NaN(), Fp16("3.4"))) },
            { FpSubExpr.class, Fp16NaN(), Sub(RNE, Fp16("5.5"), Fp16NaN()) },
            { FpPosExpr.class, Fp16NaN(), Pos(Fp16NaN()) },
            { FpNegExpr.class, Fp16NaN(), Neg(Fp16NaN()) },
            { FpMulExpr.class, Fp16NaN(), Mul(RNE, List.of(Fp16NaN(), Fp16("3.4"))) },
            { FpDivExpr.class, Fp16NaN(), Div(RNE, Fp16("7.14"), Fp16NaN()) },
        });
    }

    public static Collection<?> InfinityOperations() {
        return Arrays.asList(new Object[][] {
            { FpAddExpr.class, Fp16PInf(), Add(RNA, List.of(Fp16PInf(), Fp16("3.4"))) },
            { FpSubExpr.class, Fp16NInf(), Sub(RNA, Fp16("5.5"), Fp16PInf()) },
            { FpPosExpr.class, Fp16PInf(), Pos(Fp16PInf()) },
            { FpNegExpr.class, Fp16NInf(), Neg(Fp16PInf()) },
            { FpMulExpr.class, Fp16PInf(), Mul(RNA, List.of(Fp16PInf(), Fp16("3.4"))) },
            { FpDivExpr.class, Fp16("0"), Div(RNA, Fp16("7.14"), Fp16PInf()) },
        });
    }

    private static final BinaryMathContext BINARY16 = BinaryMathContext.BINARY16.withRoundingMode(FpUtils.getMathContextRoundingMode(RNE));

    private static FpLitExpr Fp16(final String lit) {
        return FpUtils.bigFloatToFpLitExpr(new BigFloat(lit, BINARY16), FpType(5, 11));
    }

    private static FpLitExpr Fp16NaN() {
        return FpUtils.bigFloatToFpLitExpr(BigFloat.NaN(BINARY16.precision), FpType(5, 11));
    }

    private static FpLitExpr Fp16PInf() {
        return FpUtils.bigFloatToFpLitExpr(BigFloat.positiveInfinity(BINARY16.precision), FpType(5, 11));
    }

    private static FpLitExpr Fp16NInf() {
        return FpUtils.bigFloatToFpLitExpr(BigFloat.negativeInfinity(BINARY16.precision), FpType(5, 11));
    }
}
