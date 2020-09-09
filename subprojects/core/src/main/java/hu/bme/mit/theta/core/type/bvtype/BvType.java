package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.*;

import static com.google.common.base.Preconditions.checkArgument;

public final class BvType implements Equational<BvType> {
    private final static int HASH_SEED = 5674;
    private final static String TYPE_LABEL = "Bv";

    private final int size;

    private volatile int hashCode = 0;

    private BvType(final int size) {
        checkArgument(size > 0);
        this.size = size;
    }

    public static BvType of(final int size) {
        return new BvType(size);
    }

    public int getSize() {
        return size;
    }

    @Override
    public EqExpr<BvType> Eq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvEqExpr.of(leftOp, rightOp);
    }

    @Override
    public NeqExpr<BvType> Neq(Expr<BvType> leftOp, Expr<BvType> rightOp) {
        return BvNeqExpr.of(leftOp, rightOp);
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + size;
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof BvType) {
            final BvType that = (BvType) obj;
            return this.getSize() == that.getSize();
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(TYPE_LABEL).add(size).toString();
    }
}
