package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.type.Expr;

public final class BvExprs {

    private BvExprs() {

    }

    public static BvType BvType(final int size, final boolean isSigned) {
        return BvType.of(size, isSigned);
    }

    public static BvLitExpr Bv(final boolean[] value, final boolean isSigned) {
        return BvLitExpr.of(value, isSigned);
    }

    public static BvEqExpr Eq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvEqExpr.of(leftOp, rightOp);
    }

    public static BvNeqExpr Neq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvNeqExpr.of(leftOp, rightOp);
    }
}
