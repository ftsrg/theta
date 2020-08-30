package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.type.Expr;

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

    public static BvPosExpr Pos(final Expr<BvType> op) {
        return BvPosExpr.of(op);
    }

    public static BvNegExpr Neg(final Expr<BvType> op) {
        return BvNegExpr.of(op);
    }

    public static BvMulExpr Mul(final Iterable<? extends Expr<BvType>> ops) {
        return BvMulExpr.of(ops);
    }

    public static BvDivExpr Div(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvDivExpr.of(leftOp, rightOp);
    }

    public static BvModExpr Mod(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvModExpr.of(leftOp, rightOp);
    }

    public static BvRemExpr Rem(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvRemExpr.of(leftOp, rightOp);
    }

    public static BvOrExpr Or(final List<? extends Expr<BvType>> ops) {
        return BvOrExpr.of(ops);
    }

    public static BvAndExpr And(final List<? extends Expr<BvType>> ops) {
        return BvAndExpr.of(ops);
    }

    public static BvXorExpr Xor(final List<? extends Expr<BvType>> ops) {
        return BvXorExpr.of(ops);
    }

    public static BvNotExpr Not(final Expr<BvType> op) {
        return BvNotExpr.of(op);
    }

    public static BvShiftLeftExpr ShiftLeft(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvShiftLeftExpr.of(leftOp, rightOp);
    }

    public static BvArithShiftRightExpr ArithShiftRight(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvArithShiftRightExpr.of(leftOp, rightOp);
    }

    public static BvLogicShiftRightExpr LogicShiftRight(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvLogicShiftRightExpr.of(leftOp, rightOp);
    }

    public static BvRotateLeftExpr RotateLeft(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvRotateLeftExpr.of(leftOp, rightOp);
    }

    public static BvRotateRightExpr RotateRight(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvRotateRightExpr.of(leftOp, rightOp);
    }

    public static BvEqExpr Eq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvEqExpr.of(leftOp, rightOp);
    }

    public static BvNeqExpr Neq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvNeqExpr.of(leftOp, rightOp);
    }

    public static BvLtExpr Lt(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvLtExpr.of(leftOp, rightOp);
    }

    public static BvLeqExpr Leq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvLeqExpr.of(leftOp, rightOp);
    }

    public static BvGtExpr Gt(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvGtExpr.of(leftOp, rightOp);
    }

    public static BvGeqExpr Geq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvGeqExpr.of(leftOp, rightOp);
    }

    public static BvToIntExpr ToInt(final Expr<BvType> op) {
        return BvToIntExpr.of(op);
    }
}
