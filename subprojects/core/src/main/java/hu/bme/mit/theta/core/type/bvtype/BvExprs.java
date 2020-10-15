package hu.bme.mit.theta.core.type.bvtype;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;

import java.util.List;

public final class BvExprs {

    private BvExprs() {

    }

    public static BvType BvType(final int size) {
        return BvType.of(size);
    }

    public static BvLitExpr Bv(final boolean[] value) {
        return BvLitExpr.of(value);
    }

    public static BvConcatExpr Concat(final Iterable<? extends Expr<BvType>> ops) {
        return BvConcatExpr.of(ops);
    }

    public static BvExtractExpr Extract(final Expr<BvType> bitvec, final IntLitExpr from, final IntLitExpr until) {
        return BvExtractExpr.of(bitvec, from, until);
    }

    public static BvZExtExpr ZExt(final Expr<BvType> bitvec, final BvType extendType) {
        return BvZExtExpr.of(bitvec, extendType);
    }

    public static BvSExtExpr SExt(final Expr<BvType> bitvec, final BvType extendType) {
        return BvSExtExpr.of(bitvec, extendType);
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

    public static BvUDivExpr UDiv(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvUDivExpr.of(leftOp, rightOp);
    }

    public static BvSDivExpr SDiv(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSDivExpr.of(leftOp, rightOp);
    }

    public static BvSModExpr SMod(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSModExpr.of(leftOp, rightOp);
    }

    public static BvURemExpr URem(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvURemExpr.of(leftOp, rightOp);
    }

    public static BvSRemExpr SRem(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSRemExpr.of(leftOp, rightOp);
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

    public static BvULtExpr ULt(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvULtExpr.of(leftOp, rightOp);
    }

    public static BvULeqExpr ULeq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvULeqExpr.of(leftOp, rightOp);
    }

    public static BvUGtExpr UGt(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvUGtExpr.of(leftOp, rightOp);
    }

    public static BvUGeqExpr UGeq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvUGeqExpr.of(leftOp, rightOp);
    }

    public static BvSLtExpr SLt(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSLtExpr.of(leftOp, rightOp);
    }

    public static BvSLeqExpr SLeq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSLeqExpr.of(leftOp, rightOp);
    }

    public static BvSGtExpr SGt(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSGtExpr.of(leftOp, rightOp);
    }

    public static BvSGeqExpr SGeq(final Expr<BvType> leftOp, final Expr<BvType> rightOp) {
        return BvSGeqExpr.of(leftOp, rightOp);
    }
}
