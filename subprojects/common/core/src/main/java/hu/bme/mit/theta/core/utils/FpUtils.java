package hu.bme.mit.theta.core.utils;

import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpLitExpr;
import hu.bme.mit.theta.core.type.fptype.FpRoundingMode;
import hu.bme.mit.theta.core.type.fptype.FpType;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.math.RoundingMode;

public final class FpUtils {
    private FpUtils() {}

    public static BigDecimal fpLitExprToBigDecimal(final FpRoundingMode roundingMode, final FpLitExpr expr) {
        final BigInteger exponent = BvUtils.neutralBvLitExprToBigInteger(expr.getExponent());

        BigInteger significandInteger = BvUtils.neutralBvLitExprToBigInteger(expr.getSignificand());
        if(expr.getHidden()) {
            significandInteger = significandInteger.negate();
        }

        final MathContext mathContext = getMathContext(expr.getType(), roundingMode);

        return new BigDecimal(significandInteger).multiply(BigDecimal.TEN.pow(-exponent.intValue(), mathContext), mathContext);
    }

    public static FpLitExpr bigDecimalToFpLitExpr(final BigDecimal bigDecimal, final FpType type) {
        final BvLitExpr exponent = BvUtils.bigIntegerToNeutralBvLitExpr(BigInteger.valueOf(bigDecimal.scale()), type.getExponent());

        final BigInteger significand = bigDecimal.unscaledValue();

        return FpLitExpr.of(significand.compareTo(BigInteger.ZERO) < 0, exponent, BvUtils.bigIntegerToNeutralBvLitExpr(significand.abs(), type.getSignificand()-1));
    }

    public static RoundingMode getMathContextRoundingMode(final FpRoundingMode roundingMode) {
        switch (roundingMode) {
            case RNE:
                return RoundingMode.HALF_EVEN;
            case RNA:
                return RoundingMode.UP;
            case RTP:
                return RoundingMode.CEILING;
            case RTN:
                return RoundingMode.FLOOR;
            case RTZ:
                return RoundingMode.DOWN;
            default:
                throw new UnsupportedOperationException();
        }
    }

    public static MathContext getMathContext(final FpType type, final FpRoundingMode roundingMode) {
        return new MathContext(type.getSignificand(), getMathContextRoundingMode(roundingMode));
    }
}
