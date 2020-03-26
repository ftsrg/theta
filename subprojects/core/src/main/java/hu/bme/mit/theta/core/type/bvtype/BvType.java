package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.abstracttype.EqExpr;
import hu.bme.mit.theta.core.type.abstracttype.Equational;
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr;

import static com.google.common.base.Preconditions.checkArgument;

public final class BvType implements Equational<BvType> {
    private final static int HASH_SEED = 5674;
    private final static String TYPE_LABEL = "Bv";

    private final int size;
    private final boolean isSigned;

    private volatile int hashCode = 0;

    private BvType(final int size, final boolean isSigned) {
        checkArgument(size > 0);
        this.size = size;
        this.isSigned = isSigned;
    }

    public static BvType of(final int size, final boolean isSigned) {
        return new BvType(size, isSigned);
    }

    public int getSize() {
        return size;
    }

    public boolean isSigned() {
        return isSigned;
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
            result = 31 * result + (isSigned ? 1 : 0);
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
            return this.getSize() == that.getSize() && this.isSigned() == that.isSigned();
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(TYPE_LABEL).add(size).add(isSigned ? "signed" : "unsigned").toString();
    }
}
