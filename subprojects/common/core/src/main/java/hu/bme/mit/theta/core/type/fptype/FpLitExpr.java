package hu.bme.mit.theta.core.type.fptype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.bvtype.BvLitExpr;
import hu.bme.mit.theta.core.type.bvtype.BvType;
import hu.bme.mit.theta.core.utils.FpUtils;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToNeutralBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.fitBigIntegerIntoNeutralDomain;
import static hu.bme.mit.theta.core.utils.BvUtils.neutralBvLitExprToBigInteger;

public class FpLitExpr extends NullaryExpr<FpType> implements LitExpr<FpType>, Comparable<FpType> {
    private static final int HASH_SEED = 4254;
    private volatile int hashCode = 0;

    private final boolean hidden;
    private final BvLitExpr exponent;
    private final BvLitExpr significand;

    private FpLitExpr(final boolean hidden, final BvLitExpr exponent, final BvLitExpr significand) {
        checkNotNull(exponent);
        checkNotNull(significand);

        this.hidden = hidden;
        this.exponent = exponent;
        this.significand = significand;
    }

    public static FpLitExpr of(final boolean hidden, final BvLitExpr exponent, final BvLitExpr significand) {
        return new FpLitExpr(hidden, exponent, significand);
    }

    public boolean getHidden() {
        return hidden;
    }

    public BvLitExpr getExponent() {
        return exponent;
    }

    public BvLitExpr getSignificand() {
        return significand;
    }

    public FpLitExpr add(final FpRoundingMode roundingMode, final FpLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigDecimal sum = FpUtils.fpLitExprToBigDecimal(roundingMode, this).add(FpUtils.fpLitExprToBigDecimal(roundingMode, that));
        return FpUtils.bigDecimalToFpLitExpr(sum, getType());
    }

    @Override
    public FpType getType() {
        return FpType.of(exponent.getType().getSize(), significand.getType().getSize()+1);
    }

    @Override
    public LitExpr<FpType> eval(Valuation val) {
        return this;
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + Boolean.hashCode(hidden);
            result = 31 * result + exponent.hashCode();
            result = 31 * result + significand.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof FpLitExpr) {
            final FpLitExpr that = (FpLitExpr) obj;
            return this.hidden == that.hidden && this.exponent.equals(that.exponent) && this.significand.equals(that.significand);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return
            (hidden ? "-" : "+") +
            exponent.toString() +
            "." +
            significand.toString();
    }

    @Override
    public int compareTo(FpType fpType) {
        return 0;
    }
}
