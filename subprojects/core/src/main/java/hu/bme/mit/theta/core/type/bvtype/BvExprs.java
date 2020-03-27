package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntNegExpr;
import hu.bme.mit.theta.core.type.inttype.IntSubExpr;
import hu.bme.mit.theta.core.type.inttype.IntType;

import java.util.List;

public final class BvExprs {

    private BvExprs() {

    }

    public static BvType BvType(final int size, final boolean isSigned) {
        return BvType.of(size, isSigned);
    }

    public static BvLitExpr Bv(final boolean[] value, final boolean isSigned) {
        return BvLitExpr.of(value, isSigned);
    }

    public static BvAddExpr Add(final Iterable<? extends Expr<BvType>> ops) {
        return BvAddExpr.of(ops);
    }

    public static BvSubExpr Sub(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSubExpr.of(leftOp, rightOp);
    }

    public static BvNegExpr Neg(final Expr<BvType> op) {
        return BvNegExpr.of(op);
    }

    public static BvEqExpr Eq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvEqExpr.of(leftOp, rightOp);
    }

    public static BvNeqExpr Neq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvNeqExpr.of(leftOp, rightOp);
    }
}
