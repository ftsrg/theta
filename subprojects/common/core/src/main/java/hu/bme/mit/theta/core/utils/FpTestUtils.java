package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.fptype.FpAddExpr;
import hu.bme.mit.theta.core.type.fptype.FpDivExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpMulExpr;
import hu.bme.mit.theta.core.type.fptype.FpNegExpr;
import hu.bme.mit.theta.core.type.fptype.FpPosExpr;
import hu.bme.mit.theta.core.type.fptype.FpSubExpr;
import org.kframework.mpfr.BigFloat;
import org.kframework.mpfr.BinaryMathContext;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static hu.bme.mit.theta.core.type.fptype.FpExprs.Add;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Div;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Mul;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Neg;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Pos;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.Sub;
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
