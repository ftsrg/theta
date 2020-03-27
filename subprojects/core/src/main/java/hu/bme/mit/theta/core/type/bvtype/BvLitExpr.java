package hu.bme.mit.theta.core.type.bvtype;

import static com.google.common.base.Preconditions.*;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;

import java.math.BigInteger;
import java.util.Arrays;

public final class BvLitExpr extends NullaryExpr<BvType> implements LitExpr<BvType> {

    private static final int HASH_SEED = 5624;
    private volatile int hashCode = 0;

    private final boolean[] value;
    private final boolean isSigned;

    private BvLitExpr(final boolean[] value, final boolean isSigned) {
        checkNotNull(value);
        checkArgument(value.length > 0, "Bitvector must have positive size");

        this.value = value;
        this.isSigned = isSigned;
    }

    public static BvLitExpr of(final boolean[] value, final boolean isSigned) {
        return new BvLitExpr(value, isSigned);
    }

    public boolean[] getValue() {
        return value;
    }

    public boolean isSigned() {
        return isSigned;
    }

    @Override
    public BvType getType() {
        return BvType(value.length, isSigned);
    }

    @Override
    public LitExpr<BvType> eval(Valuation val) {
        return this;
    }

    public BvLitExpr add(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger sum = BvUtils.bvLitExprToBigInteger(this).add(BvUtils.bvLitExprToBigInteger(that));
        sum = BvUtils.fitBigIntegerIntoDomain(sum, getType().getSize(), getType().isSigned());
        return BvUtils.bigIntegerToBvLitExpr(sum, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr sub(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger sub = BvUtils.bvLitExprToBigInteger(this).subtract(BvUtils.bvLitExprToBigInteger(that));
        sub = BvUtils.fitBigIntegerIntoDomain(sub, getType().getSize(), getType().isSigned());
        return BvUtils.bigIntegerToBvLitExpr(sub, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr mul(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger prod = BvUtils.bvLitExprToBigInteger(this).multiply(BvUtils.bvLitExprToBigInteger(that));
        prod = BvUtils.fitBigIntegerIntoDomain(prod, getType().getSize(), getType().isSigned());
        return BvUtils.bigIntegerToBvLitExpr(prod, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr neg() {
        BigInteger neg = BvUtils.bvLitExprToBigInteger(this).negate();
        neg = BvUtils.fitBigIntegerIntoDomain(neg, getType().getSize(), getType().isSigned());
        return BvUtils.bigIntegerToBvLitExpr(neg, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr div(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger div = BvUtils.bvLitExprToBigInteger(this).divide(BvUtils.bvLitExprToBigInteger(that));
        div = BvUtils.fitBigIntegerIntoDomain(div, getType().getSize(), getType().isSigned());
        return BvUtils.bigIntegerToBvLitExpr(div, getType().getSize(), getType().isSigned());
    }

    public BoolLitExpr eq(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(Arrays.equals(this.getValue(), that.getValue()));
    }

    public BoolLitExpr neq(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(!Arrays.equals(this.getValue(), that.getValue()));
    }

    public BoolLitExpr lt(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(BvUtils.bvLitExprToBigInteger(this).compareTo(BvUtils.bvLitExprToBigInteger(that)) < 0);
    }

    public BoolLitExpr leq(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(BvUtils.bvLitExprToBigInteger(this).compareTo(BvUtils.bvLitExprToBigInteger(that)) <= 0);
    }

    public BoolLitExpr gt(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(BvUtils.bvLitExprToBigInteger(this).compareTo(BvUtils.bvLitExprToBigInteger(that)) > 0);
    }

    public BoolLitExpr geq(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(BvUtils.bvLitExprToBigInteger(this).compareTo(BvUtils.bvLitExprToBigInteger(that)) >= 0);
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + Arrays.hashCode(value);
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvLitExpr) {
            final BvLitExpr that = (BvLitExpr) obj;
            return Arrays.equals(this.value, that.value);
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Arrays.toString(value)
            .replace("true", "1")
            .replace("false", "0")
            .replace("[", "")
            .replace("]", "")
            .replace(",", "")
            .replace(" ", "");
    }
}
