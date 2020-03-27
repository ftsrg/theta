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
