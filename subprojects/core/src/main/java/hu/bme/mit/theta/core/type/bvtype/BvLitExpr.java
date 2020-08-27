package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.NullaryExpr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.utils.BvUtils;

import java.math.BigInteger;
import java.util.Arrays;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.Bv;
import static hu.bme.mit.theta.core.type.bvtype.BvExprs.BvType;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public final class BvLitExpr extends NullaryExpr<BvType> implements LitExpr<BvType>, Comparable<BvLitExpr> {

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

    public BvLitExpr pos() {
        BigInteger pos = BvUtils.bvLitExprToBigInteger(this);
        pos = BvUtils.fitBigIntegerIntoDomain(pos, getType().getSize(), getType().isSigned());
        return BvUtils.bigIntegerToBvLitExpr(pos, getType().getSize(), getType().isSigned());
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

    public BvLitExpr and(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger and = BvUtils.bvLitExprToBigInteger(this).and(BvUtils.bvLitExprToBigInteger(that));
        return BvUtils.bigIntegerToBvLitExpr(and, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr or(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger or = BvUtils.bvLitExprToBigInteger(this).or(BvUtils.bvLitExprToBigInteger(that));
        return BvUtils.bigIntegerToBvLitExpr(or, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr xor(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger xor = BvUtils.bvLitExprToBigInteger(this).xor(BvUtils.bvLitExprToBigInteger(that));
        return BvUtils.bigIntegerToBvLitExpr(xor, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr not() {
        BigInteger not = BvUtils.bvLitExprToBigInteger(this).not();
        return BvUtils.bigIntegerToBvLitExpr(not, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr shiftLeft(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        for(BigInteger i = BigInteger.ZERO; i.compareTo(BvUtils.bvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            for(int j = 0; j < shifted.length - 1; j++) {
                shifted[j] = shifted[j + 1];
            }
            shifted[shifted.length - 1] = false;
        }
        return Bv(shifted, getType().isSigned());
    }

    public BvLitExpr arithShiftRight(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        boolean insert = shifted[0];
        for(BigInteger i = BigInteger.ZERO; i.compareTo(BvUtils.bvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            for(int j = shifted.length - 1; j > 0; j--) {
                shifted[j] = shifted[j - 1];
            }
            shifted[0] = insert;
        }
        return Bv(shifted, getType().isSigned());
    }

    public BvLitExpr logicShiftRight(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        boolean insert = false;
        for(BigInteger i = BigInteger.ZERO; i.compareTo(BvUtils.bvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            for(int j = shifted.length - 1; j > 0; j--) {
                shifted[j] = shifted[j - 1];
            }
            shifted[0] = insert;
        }
        return Bv(shifted, getType().isSigned());
    }

    public BvLitExpr rotateLeft(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        for(BigInteger i = BigInteger.ZERO; i.compareTo(BvUtils.bvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            boolean rotated = shifted[0];
            for(int j = 0; j < shifted.length - 1; j++) {
                shifted[j] = shifted[j + 1];
            }
            shifted[shifted.length - 1] = rotated;
        }
        return Bv(shifted, getType().isSigned());
    }

    public BvLitExpr rotateRight(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        for(BigInteger i = BigInteger.ZERO; i.compareTo(BvUtils.bvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            boolean rotated = shifted[shifted.length - 1];
            for(int j = shifted.length - 1; j > 0; j--) {
                shifted[j] = shifted[j - 1];
            }
            shifted[0] = rotated;
        }
        return Bv(shifted, getType().isSigned());
    }

    public BvLitExpr mod(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        // Always positive semantics:
        // 5 mod 3 = 2
        // 5 mod -3 = 2
        // -5 mod 3 = 1
        // -5 mod -3 = 1
        BigInteger result = BvUtils.bvLitExprToBigInteger(this).mod(BvUtils.bvLitExprToBigInteger(that));
        if (result.compareTo(BigInteger.ZERO) < 0) {
            result = result.add(BvUtils.bvLitExprToBigInteger(that).abs());
        }
        assert result.compareTo(BigInteger.ZERO) >= 0;
        return BvUtils.bigIntegerToBvLitExpr(result, getType().getSize(), getType().isSigned());
    }

    public BvLitExpr rem(final BvLitExpr that) {
        // Semantics:
        // 5 rem 3 = 2
        // 5 rem -3 = 2
        // -5 rem 3 = -1
        // -5 rem -3 = -1
        BigInteger thisInt = BvUtils.bvLitExprToBigInteger(this);
        BigInteger thatInt = BvUtils.bvLitExprToBigInteger(that);
        BigInteger thisAbs = thisInt.abs();
        BigInteger thatAbs = thatInt.abs();
        if (thisInt.compareTo(BigInteger.ZERO) < 0 && thatInt.compareTo(BigInteger.ZERO) < 0) {
            return BvUtils.bigIntegerToBvLitExpr(thisAbs.mod(thatAbs).negate(), getType().getSize(), getType().isSigned());
        } else if (thisInt.compareTo(BigInteger.ZERO) >= 0 && thatInt.compareTo(BigInteger.ZERO) < 0) {
            return BvUtils.bigIntegerToBvLitExpr(thisAbs.mod(thatAbs), getType().getSize(), getType().isSigned());
        } else if (thisInt.compareTo(BigInteger.ZERO) < 0 && thatInt.compareTo(BigInteger.ZERO) >= 0) {
            return BvUtils.bigIntegerToBvLitExpr(thisAbs.mod(thatAbs).negate(), getType().getSize(), getType().isSigned());
        } else {
            return BvUtils.bigIntegerToBvLitExpr(thisInt.mod(thatInt), getType().getSize(), getType().isSigned());
        }
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

    public IntLitExpr toInt() {
        return Int(BvUtils.bvLitExprToBigInteger(this));
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

    @Override
    public int compareTo(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return BvUtils.bvLitExprToBigInteger(this).compareTo(BvUtils.bvLitExprToBigInteger(that));
    }
}
