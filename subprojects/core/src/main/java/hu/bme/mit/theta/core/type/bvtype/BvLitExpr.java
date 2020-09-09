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
import static hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToNeutralBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToSignedBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.bigIntegerToUnsignedBvLitExpr;
import static hu.bme.mit.theta.core.utils.BvUtils.fitBigIntegerIntoNeutralDomain;
import static hu.bme.mit.theta.core.utils.BvUtils.fitBigIntegerIntoSignedDomain;
import static hu.bme.mit.theta.core.utils.BvUtils.fitBigIntegerIntoUnsignedDomain;
import static hu.bme.mit.theta.core.utils.BvUtils.neutralBvLitExprToBigInteger;
import static hu.bme.mit.theta.core.utils.BvUtils.signedBvLitExprToBigInteger;
import static hu.bme.mit.theta.core.utils.BvUtils.unsignedBvLitExprToBigInteger;

public final class BvLitExpr extends NullaryExpr<BvType> implements LitExpr<BvType>, Comparable<BvLitExpr> {

    private static final int HASH_SEED = 5624;
    private volatile int hashCode = 0;

    private final boolean[] value;

    private BvLitExpr(final boolean[] value) {
        checkNotNull(value);
        checkArgument(value.length > 0, "Bitvector must have positive size");

        this.value = value;
    }

    public static BvLitExpr of(final boolean[] value) {
        return new BvLitExpr(value);
    }

    public boolean[] getValue() {
        return value;
    }

    @Override
    public BvType getType() {
        return BvType(value.length);
    }

    @Override
    public LitExpr<BvType> eval(Valuation val) {
        return this;
    }

    public BvLitExpr concat(final BvLitExpr that) {
        boolean[] concated = new boolean[this.getType().getSize() + that.getType().getSize()];
        for(int i = 0; i < this.getType().getSize(); i++) {
            concated[i] = this.getValue()[i];
        }
        for(int i = 0; i < that.getType().getSize(); i++) {
            concated[this.getType().getSize() + i] = that.getValue()[i];
        }
        return Bv(concated);
    }

    public BvLitExpr extract(final IntLitExpr from, final IntLitExpr until) {
        final int fromValue = from.getValue().intValue();
        final int untilValue = until.getValue().intValue();
        checkArgument(fromValue >= 0);
        checkArgument(untilValue >= 0);
        checkArgument(untilValue > fromValue);

        boolean[] extracted = new boolean[untilValue - fromValue];
        for(int i = 0; i < extracted.length; i++) {
            extracted[extracted.length - i - 1] = this.getValue()[this.getValue().length - (fromValue + i) - 1];
        }
        return Bv(extracted);
    }

    public BvLitExpr zext(final BvType extendType) {
        checkArgument(extendType.getSize() >= this.getType().getSize());

        boolean[] extended = new boolean[extendType.getSize()];
        for(int i = 0; i < this.getValue().length; i++) {
            extended[extended.length - i - 1] = this.getValue()[this.getValue().length - i - 1];
        }
        for(int i = 0; i < extendType.getSize() - this.getType().getSize(); i++) {
            extended[i] = false;
        }
        return Bv(extended);
    }

    public BvLitExpr sext(final BvType extendType) {
        checkArgument(extendType.getSize() >= this.getType().getSize());

        boolean[] extended = new boolean[extendType.getSize()];
        for(int i = 0; i < this.getValue().length; i++) {
            extended[extended.length - i - 1] = this.getValue()[this.getValue().length - i - 1];
        }
        for(int i = 0; i < extendType.getSize() - this.getType().getSize(); i++) {
            extended[i] = this.getValue()[0];
        }
        return Bv(extended);
    }

    public BvLitExpr add(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger sum = neutralBvLitExprToBigInteger(this).add(neutralBvLitExprToBigInteger(that));
        sum = fitBigIntegerIntoNeutralDomain(sum, getType().getSize());
        return bigIntegerToNeutralBvLitExpr(sum, getType().getSize());
    }

    public BvLitExpr sub(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger sub = neutralBvLitExprToBigInteger(this).subtract(neutralBvLitExprToBigInteger(that));
        sub = fitBigIntegerIntoNeutralDomain(sub, getType().getSize());
        return bigIntegerToNeutralBvLitExpr(sub, getType().getSize());
    }

    public BvLitExpr mul(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger prod = neutralBvLitExprToBigInteger(this).multiply(neutralBvLitExprToBigInteger(that));
        prod = fitBigIntegerIntoNeutralDomain(prod, getType().getSize());
        return bigIntegerToNeutralBvLitExpr(prod, getType().getSize());
    }

    public BvLitExpr pos() {
        BigInteger pos = signedBvLitExprToBigInteger(this);
        pos = fitBigIntegerIntoSignedDomain(pos, getType().getSize());
        return bigIntegerToSignedBvLitExpr(pos, getType().getSize());
    }

    public BvLitExpr neg() {
        BigInteger neg = signedBvLitExprToBigInteger(this).negate();
        neg = fitBigIntegerIntoSignedDomain(neg, getType().getSize());
        return bigIntegerToSignedBvLitExpr(neg, getType().getSize());
    }

    public BvLitExpr udiv(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger div = unsignedBvLitExprToBigInteger(this).divide(unsignedBvLitExprToBigInteger(that));
        div = fitBigIntegerIntoUnsignedDomain(div, getType().getSize());
        return bigIntegerToUnsignedBvLitExpr(div, getType().getSize());
    }

    public BvLitExpr sdiv(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger div = signedBvLitExprToBigInteger(this).divide(signedBvLitExprToBigInteger(that));
        div = fitBigIntegerIntoSignedDomain(div, getType().getSize());
        return bigIntegerToSignedBvLitExpr(div, getType().getSize());
    }

    public BvLitExpr and(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger and = neutralBvLitExprToBigInteger(this).and(neutralBvLitExprToBigInteger(that));
        return bigIntegerToNeutralBvLitExpr(and, getType().getSize());
    }

    public BvLitExpr or(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger or = neutralBvLitExprToBigInteger(this).or(neutralBvLitExprToBigInteger(that));
        return bigIntegerToNeutralBvLitExpr(or, getType().getSize());
    }

    public BvLitExpr xor(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        BigInteger xor = neutralBvLitExprToBigInteger(this).xor(neutralBvLitExprToBigInteger(that));
        return bigIntegerToNeutralBvLitExpr(xor, getType().getSize());
    }

    public BvLitExpr not() {
        BigInteger not = neutralBvLitExprToBigInteger(this).not();
        return bigIntegerToNeutralBvLitExpr(not, getType().getSize());
    }

    public BvLitExpr shiftLeft(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        for(BigInteger i = BigInteger.ZERO; i.compareTo(neutralBvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            for(int j = 0; j < shifted.length - 1; j++) {
                shifted[j] = shifted[j + 1];
            }
            shifted[shifted.length - 1] = false;
        }
        return Bv(shifted);
    }

    public BvLitExpr arithShiftRight(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        boolean insert = shifted[0];
        for(BigInteger i = BigInteger.ZERO; i.compareTo(neutralBvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            for(int j = shifted.length - 1; j > 0; j--) {
                shifted[j] = shifted[j - 1];
            }
            shifted[0] = insert;
        }
        return Bv(shifted);
    }

    public BvLitExpr logicShiftRight(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        boolean insert = false;
        for(BigInteger i = BigInteger.ZERO; i.compareTo(neutralBvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            for(int j = shifted.length - 1; j > 0; j--) {
                shifted[j] = shifted[j - 1];
            }
            shifted[0] = insert;
        }
        return Bv(shifted);
    }

    public BvLitExpr rotateLeft(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        for(BigInteger i = BigInteger.ZERO; i.compareTo(neutralBvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            boolean rotated = shifted[0];
            for(int j = 0; j < shifted.length - 1; j++) {
                shifted[j] = shifted[j + 1];
            }
            shifted[shifted.length - 1] = rotated;
        }
        return Bv(shifted);
    }

    public BvLitExpr rotateRight(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));

        boolean[] shifted = Arrays.copyOf(this.getValue(), this.getValue().length);
        for(BigInteger i = BigInteger.ZERO; i.compareTo(neutralBvLitExprToBigInteger(that)) < 0; i = i.add(BigInteger.ONE)) {
            boolean rotated = shifted[shifted.length - 1];
            for(int j = shifted.length - 1; j > 0; j--) {
                shifted[j] = shifted[j - 1];
            }
            shifted[0] = rotated;
        }
        return Bv(shifted);
    }

    public BvLitExpr smod(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        // Always positive semantics:
        // 5 mod 3 = 2
        // 5 mod -3 = 2
        // -5 mod 3 = 1
        // -5 mod -3 = 1
        BigInteger result = signedBvLitExprToBigInteger(this).mod(signedBvLitExprToBigInteger(that));
        if (result.compareTo(BigInteger.ZERO) < 0) {
            result = result.add(signedBvLitExprToBigInteger(that).abs());
        }
        assert result.compareTo(BigInteger.ZERO) >= 0;
        return bigIntegerToSignedBvLitExpr(result, getType().getSize());
    }

    public BvLitExpr urem(final BvLitExpr that) {
        // Semantics:
        // 5 rem 3 = 2
        BigInteger thisInt = signedBvLitExprToBigInteger(this);
        BigInteger thatInt = signedBvLitExprToBigInteger(that);
        return bigIntegerToSignedBvLitExpr(thisInt.mod(thatInt), getType().getSize());
    }

    public BvLitExpr srem(final BvLitExpr that) {
        // Semantics:
        // 5 rem 3 = 2
        // 5 rem -3 = 2
        // -5 rem 3 = -1
        // -5 rem -3 = -1
        BigInteger thisInt = BvUtils.signedBvLitExprToBigInteger(this);
        BigInteger thatInt = BvUtils.signedBvLitExprToBigInteger(that);
        BigInteger thisAbs = thisInt.abs();
        BigInteger thatAbs = thatInt.abs();
        if (thisInt.compareTo(BigInteger.ZERO) < 0 && thatInt.compareTo(BigInteger.ZERO) < 0) {
            return bigIntegerToSignedBvLitExpr(thisAbs.mod(thatAbs).negate(), getType().getSize());
        } else if (thisInt.compareTo(BigInteger.ZERO) >= 0 && thatInt.compareTo(BigInteger.ZERO) < 0) {
            return bigIntegerToSignedBvLitExpr(thisAbs.mod(thatAbs), getType().getSize());
        } else if (thisInt.compareTo(BigInteger.ZERO) < 0 && thatInt.compareTo(BigInteger.ZERO) >= 0) {
            return bigIntegerToSignedBvLitExpr(thisAbs.mod(thatAbs).negate(), getType().getSize());
        } else {
            return bigIntegerToSignedBvLitExpr(thisInt.mod(thatInt), getType().getSize());
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

    public BoolLitExpr ult(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(unsignedBvLitExprToBigInteger(this).compareTo(unsignedBvLitExprToBigInteger(that)) < 0);
    }

    public BoolLitExpr ule(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(unsignedBvLitExprToBigInteger(this).compareTo(unsignedBvLitExprToBigInteger(that)) <= 0);
    }

    public BoolLitExpr ugt(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(unsignedBvLitExprToBigInteger(this).compareTo(unsignedBvLitExprToBigInteger(that)) > 0);
    }

    public BoolLitExpr uge(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(unsignedBvLitExprToBigInteger(this).compareTo(unsignedBvLitExprToBigInteger(that)) >= 0);
    }

    public BoolLitExpr slt(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(signedBvLitExprToBigInteger(this).compareTo(signedBvLitExprToBigInteger(that)) < 0);
    }

    public BoolLitExpr sle(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(signedBvLitExprToBigInteger(this).compareTo(signedBvLitExprToBigInteger(that)) <= 0);
    }

    public BoolLitExpr sgt(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(signedBvLitExprToBigInteger(this).compareTo(signedBvLitExprToBigInteger(that)) > 0);
    }

    public BoolLitExpr sge(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return Bool(signedBvLitExprToBigInteger(this).compareTo(signedBvLitExprToBigInteger(that)) >= 0);
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
        final StringBuilder sb = new StringBuilder();
        sb.append(getType().getSize());
        sb.append("'b");
        for(boolean bit : value) {
            sb.append(bit ? "1" : "0");
        }
        return sb.toString();
    }

    @Override
    public int compareTo(final BvLitExpr that) {
        checkArgument(this.getType().equals(that.getType()));
        return neutralBvLitExprToBigInteger(this).compareTo(neutralBvLitExprToBigInteger(that));
    }
}
